from pysmt.smtlib.parser import SmtLibParser

def open_(fname):
    """Transparently handle .bz2 files."""
    if fname.endswith(".bz2"):
        import bz2
        return bz2.open(fname, "rt")
    return open(fname)


def get_formula(script_stream, environment=None):
    """
    Returns the formula asserted at the end of the given script

    script_stream is a file descriptor.
    """
    mgr = None
    if environment is not None:
        mgr = environment.formula_manager

    parser = ExtendedSmtLibParser(environment)
    script = parser.get_script(script_stream)
    return script.get_last_formula(mgr)


def get_formula_strict(script_stream, environment=None):
    """Returns the formula defined in the SMTScript.

    This function assumes that only one formula is defined in the
    SMTScript. It will raise an exception if commands such as pop and
    push are present in the script, or if check-sat is called more
    than once.
    """
    mgr = None
    if environment is not None:
        mgr = environment.formula_manager

    parser = ExtendedSmtLibParser(environment)
    script = parser.get_script(script_stream)
    return script.get_strict_formula(mgr)


def get_formula_fname(script_fname, environment=None, strict=True):
    """Returns the formula asserted at the end of the given script."""
    with open_(script_fname) as script:
        if strict:
            return get_formula_strict(script, environment)
        else:
            return get_formula(script, environment)

class ExtendedSmtLibParser(SmtLibParser):
    def __init__(self, environment=None, interactive=False):
        super().__init__(environment, interactive)

        # Register new parsers
        self.interpreted["ramsey"] = self._enter_ramsey
        self.interpreted["mod"] = self._operator_adapter(self._modulo)
        self.interpreted["to_int"] = self._operator_adapter(self._to_int)

    def _enter_ramsey(self, stack, tokens, key):
        """
        Parse a (ramsey ...) construct.
        Syntax 1 (Uniform): (ramsey Int (x y) (a b) phi)
        Syntax 2 (Explicit): (ramsey ((x Int) (y Int)) ((a Int) (b Int)) phi)
        """
        
        # Detect typing mode
        tok = tokens.consume()
        is_explicit = False
        ty = None

        if tok == '(':
            # Could be start of explicit vars: ((x Int)...)
            # Or start of (Int)
            next_tok = tokens.consume()
            if next_tok == '(':
                # Pattern is (( ... -> Explicit variable list
                is_explicit = True
                tokens.add_extra_token(next_tok) 
                tokens.add_extra_token(tok)      
            else:
                # We consumed '(' and 'Sym'. We need to parse the Type.
                tokens.add_extra_token(next_tok)
                tokens.add_extra_token(tok)
                ty = self.parse_type(tokens, "expression")
        else:
            # Pattern is Sym ... -> Uniform Type (e.g. Int)
            tokens.add_extra_token(tok)
            ty = self.parse_type(tokens, "expression")

        # Helper to parse one list of variables
        def parse_var_list():
            vrs = []
            self.consume_opening(tokens, "expression")
            while True:
                name = tokens.consume()
                if name == ')':
                    break
                
                if is_explicit:
                    if name != '(':
                        raise Exception("Expected '(' in explicit var list")
                    
                    vname = self.parse_atom(tokens, "expression")
                    typename = self.parse_type(tokens, "expression")
                    self.consume_closing(tokens, "expression")
                    
                    var = self.env.formula_manager.Symbol(vname, typename)
                else:
                    vname = name
                    var = self.env.formula_manager.Symbol(vname, ty)

                self.cache.bind(vname, var)
                vrs.append((vname, var))
            return vrs

        vrs1 = parse_var_list()
        vrs2 = parse_var_list()

        # FIXED: Signature changed from (stack, tokens, key, args) to (*args)
        def _exit_ramsey(*args):
            # args contains the parsed children (the body formula)
            if len(args) != 1:
                 raise Exception("Ramsey expects exactly one body formula")
            body = args[0]
            
            # Unbind variables
            for name, _ in vrs1 + vrs2:
                self.cache.unbind(name)

            syms1 = [var for _, var in vrs1]
            syms2 = [var for _, var in vrs2]

            return self.env.formula_manager.Ramsey(syms1, syms2, body)

        # Push the exit callback onto the current stack frame
        stack[-1].append(_exit_ramsey)

    def _modulo(self, left, right):
        return self.env.formula_manager.Mod(left, right)

    def _to_int(self, arg):
        return self.env.formula_manager.ToInt(arg)
