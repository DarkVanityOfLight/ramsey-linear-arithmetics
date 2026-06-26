from typing import List, cast, Tuple
from pysmt.shortcuts import FreshSymbol, Function, FunctionType
from ramsey_extensions.formula import ExtendedFNode

from ramsey_extensions.shortcuts import Ramsey

def eliminate_existential_quantifier(formula: ExtendedFNode) -> ExtendedFNode:
    assert formula.is_ramsey()

    # If there's no existential quantifier, return unchanged
    if not formula.arg(0).is_exists():
        return formula

    ex_vars: List[ExtendedFNode] = list(formula.arg(0).quantifier_vars())
    subformula = formula.arg(0).arg(0)

    x_vars, y_vars = cast(Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]], formula.quantifier_vars())
    formals = x_vars + y_vars
    replacement = {}
    for variable in ex_vars:
        skolem = FreshSymbol(FunctionType(variable.get_type(), [arg.get_type() for arg in formals]))
        replacement[variable] = Function(skolem, formals)

    return Ramsey(list(x_vars), list(y_vars), subformula.substitute(replacement))
