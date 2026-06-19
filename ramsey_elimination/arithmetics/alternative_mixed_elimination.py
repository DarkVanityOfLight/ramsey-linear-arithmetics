from dataclasses import dataclass, field

from typing import Dict, List, Tuple, cast

from pysmt.exceptions import PysmtTypeError
from pysmt.shortcuts import And, LE, LT, Equals, Exists, FreshSymbol, Implies, Int, Not, NotEquals, Or, Plus, Real, Symbol, ToReal

from ramsey_elimination.arithmetics.existential_elimination import eliminate_existential_quantifier
from ramsey_elimination.formula_utils import ast_to_terms, bool_vector, collect_atoms, fresh_bool_vector, fresh_int_vector, fresh_real_vector, map_atoms, reconstruct_from_coeff_map
from ramsey_elimination.arithmetics.integer_elimination import eliminate_eq_atom_int, eliminate_inequality_atom_int
from ramsey_elimination.arithmetics.real_elimination import eliminate_equality_atom_real, eliminate_inequality_atom_real
from ramsey_elimination.simplifications import SumOfTerms, arithmetic_solver, make_mixed_input_format
from ramsey_extensions.fnode import ExtendedFNode
import pysmt.typing as typ

from math import floor

from ramsey_extensions.shortcuts import Ramsey



@dataclass
class EqualityDecomposition:
    pure_atoms: ExtendedFNode
    bridge_atom: ExtendedFNode
    int_bridge_var: ExtendedFNode = field(kw_only=True)
    real_bridge_var: ExtendedFNode = field(kw_only=True)

@dataclass
class StrictInequalityDecomposition:
    pure_atoms: ExtendedFNode
    bridge: ExtendedFNode
    int_bridge_var: ExtendedFNode = field(kw_only=True)
    real_bridge_var: ExtendedFNode = field(kw_only=True)
    real_dummy: ExtendedFNode = field(kw_only=True)


@dataclass
class BridgeElimination:
    v1a: Tuple[ExtendedFNode, ...]
    v2a: Tuple[ExtendedFNode, ...]
    v1a0: Tuple[ExtendedFNode, ...]
    v2a0: Tuple[ExtendedFNode, ...]

    v1d: Tuple[ExtendedFNode, ...]
    v2d: Tuple[ExtendedFNode, ...]
    v1dc: Tuple[ExtendedFNode, ...]
    v2dc: Tuple[ExtendedFNode, ...]
    v1dinf: Tuple[ExtendedFNode, ...]
    v2dinf: Tuple[ExtendedFNode, ...]



# s = 0 => real finite, int infinite
# s = 1 => int finite, real infinite
# s = 2 => int infinite, real infinite

# We collect one atom for each of these

@dataclass
class MixedEqualityEliminationResult:
    var: ExtendedFNode
    finite_real_clique: ExtendedFNode
    finite_int_clique: ExtendedFNode
    infinite_int_clique: ExtendedFNode
    infinite_real_clique: ExtendedFNode

    finite_real_bridge: ExtendedFNode
    finite_int_bridge: ExtendedFNode
    mixed_infinite_bridge: ExtendedFNode

@dataclass
class MixedInequalityEliminationResult:
    
    var: ExtendedFNode
    skeleton: ExtendedFNode
    skeleton_vars: Tuple[ExtendedFNode]

    int_admissibility: ExtendedFNode
    real_admissibility: ExtendedFNode

    # Assume these are of the form AND p_i -> a_i
    finite_real_clique: ExtendedFNode
    finite_int_clique: ExtendedFNode
    infinite_int_clique: ExtendedFNode
    infinite_real_clique: ExtendedFNode

    finite_real_bridge: ExtendedFNode
    finite_int_bridge: ExtendedFNode
    mixed_infinite_bridge: ExtendedFNode


type Decomposition = EqualityDecomposition | StrictInequalityDecomposition
type MixedEliminationResult = MixedEqualityEliminationResult | MixedInequalityEliminationResult

def split_terms(terms: SumOfTerms) -> Tuple[SumOfTerms, SumOfTerms]:
    """
    Given a SumOfTerms mapping,
    return (SumOfTerms(integer only), SumOfTerms(real only))
    """
    ints = {}
    reals = {}
    for variable, coeff in terms.items():
        if variable.symbol_type() == typ.INT:
            ints[variable] = coeff
        elif variable.symbol_type() == typ.REAL:
            reals[variable] = coeff
        else:
            raise PysmtTypeError(f"Expeceted real or integer symbol got: {variable}")

    return ints, reals

def decompose_equality(phi: ExtendedFNode) -> EqualityDecomposition:
    assert phi.is_equals()

    left, left_c = ast_to_terms(phi.arg(0))
    right, right_c = ast_to_terms(phi.arg(1))
    var_terms, _, C = arithmetic_solver(left, left_c, right, right_c, set())

    int_terms, real_terms = split_terms(var_terms)
    int_bridge = FreshSymbol(typ.INT, "c_i%s")
    real_bridge = FreshSymbol(typ.REAL, "c_r%s")

    C_i = floor(C)
    C_r = C - C_i
    real_part = Equals(reconstruct_from_coeff_map(real_terms, 0, typ.REAL),
                       Plus(real_bridge, Real(C_r)))
    int_part = Equals(
        Plus(reconstruct_from_coeff_map(int_terms, 0, typ.INT), int_bridge),
        Int(C_i)
    )

    bridge = Equals(real_bridge, ToReal(int_bridge))
    return EqualityDecomposition(And(real_part, int_part), bridge, int_bridge_var=int_bridge, real_bridge_var=real_bridge)

def decompose_inequality(phi: ExtendedFNode) -> StrictInequalityDecomposition:
    assert phi.is_lt() or phi.is_le()

    left, left_c = ast_to_terms(phi.arg(0))
    right, right_c = ast_to_terms(phi.arg(1))
    var_terms, _, C = arithmetic_solver(left, left_c, right, right_c, set())

    int_terms, real_terms = split_terms(var_terms)
    int_bridge: ExtendedFNode = FreshSymbol(typ.INT, "c_i%s")
    real_bridge: ExtendedFNode = FreshSymbol(typ.REAL, "c_r%s")
    real_dummy: ExtendedFNode = FreshSymbol(typ.REAL, "R_%s")

    C_i = floor(C)
    C_r = C - C_i

    real_part: ExtendedFNode = Equals(reconstruct_from_coeff_map(real_terms, 0, typ.REAL),
                       Plus(real_dummy, real_bridge))

    dummy_restriction: Tuple[ExtendedFNode, ExtendedFNode] = (LE(Real(0), real_dummy), LT(real_dummy, Real(1)))
    int_reconstructed: ExtendedFNode = Plus(reconstruct_from_coeff_map(int_terms, 0, typ.INT), int_bridge)
    
    int_ineq = LT(int_reconstructed, Int(C_i))
    real_ineq = And(Equals(int_reconstructed, Int(C_i)), LT(real_dummy, Real(C_r)))
    bridge: ExtendedFNode = Equals(real_bridge, ToReal(int_bridge))

    return StrictInequalityDecomposition(
        And(real_part, *dummy_restriction, Or(int_ineq, real_ineq),), bridge,
        int_bridge_var=int_bridge, real_bridge_var=real_bridge, real_dummy=real_dummy
    )


def eliminate_bridge_atom(*,v1_dc, v2_dc, v1_a, v1_dinf, w2_a, w2_dinf, v1_a0, w2_a0, v1_d0, w2_d0):
    dc_conditions = And(
        Equals(v1_dc, Real(0)), Equals(v2_dc, Real(0))
    )
    step_conditions = And(
        Equals(ToReal(v1_a), v1_dinf), Equals(ToReal(w2_a), w2_dinf)
    )
    start_conditions = And(
        Equals(ToReal(Plus(v1_a0, w2_a0)), Plus(v1_d0, w2_d0))
    )

    return And(dc_conditions, step_conditions, start_conditions)

def eliminate_ramsey_mixed(phi: ExtendedFNode):
    """
    Eliminate a mixed LIA/LRA Ramsey quantifier.
    Assumes `phi` is a Ramsey quantifier, where the subformula
    is free of existential quantifiers and in the mixed input format.
    """
    assert phi.is_ramsey()

    vars1, vars2 = phi.quantifier_vars()

    new_vars = []
    bridge_pairs = []
    def eliminator(atom: ExtendedFNode):
        if len({v.get_type() for v in atom.get_free_variables()}) > 1:
            if atom.is_equals():
                eq_result: EqualityDecomposition = decompose_equality(atom)
                new_vars.extend((eq_result.real_bridge_var, eq_result.int_bridge_var))
                bridge_pairs.append((eq_result.int_bridge_var, eq_result.real_bridge_var))
                return And(eq_result.pure_atoms, eq_result.bridge_atom)
            elif atom.is_lt():
                ineq_result: StrictInequalityDecomposition = decompose_inequality(atom)
                new_vars.extend((ineq_result.real_bridge_var, ineq_result.int_bridge_var, ineq_result.real_dummy))
                bridge_pairs.append((ineq_result.int_bridge_var, ineq_result.real_bridge_var))
                return And(ineq_result.pure_atoms, ineq_result.bridge)
            else:
                raise Exception(f"Unreachable unknown atom type in mixed elimination {atom}")
        else:
            return atom

    phi_pp = map_atoms(phi.arg(0), eliminator)

    phi_ppp, mapping = eliminate_existential_quantifier(Ramsey(vars1, vars2, Exists(new_vars, phi_pp)))

    reverse_mapping = {}
    for orig_var, ((v1, v2), (w1, w2)) in mapping.items():
        val = ((v1, v2), (w1, w2))
        reverse_mapping[v1] = val
        reverse_mapping[v2] = val
        reverse_mapping[w1] = val
        reverse_mapping[w2] = val

    new_vars1, new_vars2 = phi_ppp.quantifier_vars()
    real_vars1, real_vars2 = [var for var in new_vars1 if var.symbol_type() == typ.REAL], [var for var in new_vars2 if var.symbol_type() == typ.REAL]
    int_vars1, int_vars2 = [var for var in new_vars1 if var.symbol_type() == typ.INT], [var for var in new_vars2 if var.symbol_type() == typ.INT]

    # from benchmarks.benchmark_utils import get_atoms, get_variables
    # print(f"After decomposition Variables: {get_variables(phi_ppp)}")
    # print(f"After decomposition Atoms: {get_atoms(phi_ppp)}")

    eqs, _, ineqs = collect_atoms(phi_ppp)

    real_eqs = []
    int_eqs = []
    bridge_eqs: List[ExtendedFNode] = []
    for eq in eqs:
        types = {v.get_type() for v in eq.get_free_variables()}
        if len(types) > 1:
            bridge_eqs.append(eq)
        elif typ.INT in types:
            int_eqs.append(eq)
        elif typ.REAL in types:
            real_eqs.append(eq)
        else:
            raise Exception(f"Unknown type in atom {eq}")

    int_ineqs = []
    real_ineqs = []
    for ineq in ineqs:
        types = {v.get_type() for v in ineq.get_free_variables()}
        if len(types) > 1:
            raise Exception(f"Unknown types in atom {ineq}")
        elif typ.INT in types:
            int_ineqs.append(ineq)
        elif typ.REAL in types:
            real_ineqs.append(ineq)
        else:
            raise Exception(f"Unknown type in atom {ineq}")

    qs = fresh_bool_vector("q_{}_%s", len(eqs) + len(ineqs))
    q_mapping = {atom: qs[i] for i, atom in enumerate(eqs + ineqs) }
    skel = phi_ppp.arg(0).substitute(q_mapping)


    # INT Clique stuff
    o = len(int_vars1)
    # --- New symbolic integer vectors ---
    a0 = fresh_int_vector("a0_{}_%s", o)
    a  = fresh_int_vector("a_{}_%s", o)
    a_restriction = Or([NotEquals(a[i], Int(0)) for i in range(o)])  # nontrivial a

    # --- Profile variables for int inequalities ---
    p, omega = fresh_int_vector("p_{}_%s", 2*len(int_ineqs)), fresh_bool_vector("o_{}_%s", 2*len(int_ineqs))
    int_admissible = And([
        Or(And(Not(omega[2*i]), LT(p[2*i], p[2*i+1])), omega[2*i+1])
        for i in range(len(int_ineqs))
    ])

    def pairwise(seq):
        return [(seq[2*i], seq[2*i+1]) for i in range(len(seq)//2)]

    ineq_aux = list(zip(int_ineqs, pairwise(p), pairwise(omega)))
    ineq_iter = iter(ineq_aux)

    # --- Eliminate each int atom ---
    phi_delta_p = []
    for atom in int_eqs + int_ineqs:
        if atom in int_ineqs:
            _, p_i, omega_i = next(filter(lambda item: item[0] == atom, ineq_aux))
            phi_delta_p.append(Implies(q_mapping[atom], eliminate_inequality_atom_int(atom, int_vars1, int_vars2, omega_i, p_i, a, a0)))
        else:
            phi_delta_p.append(Implies(q_mapping[atom], eliminate_eq_atom_int(atom, int_vars1, int_vars2, a, a0)))

    theta_i = And(int_admissible, a_restriction)

    # Real clique elimination
    l, n = len(real_vars1), len(real_ineqs)
    # Fresh vectors
    rho, sigma      = fresh_real_vector("rho_{}_%s", n), fresh_real_vector("sigma_{}_%s", n)
    t_rho, t_sigma  = fresh_real_vector("t_rho_{}_%s", n), fresh_real_vector("t_sigma_{}_%s", n)
    d, d_c, d_inf   = (fresh_real_vector(prefix, l) for prefix in ("x_{}_%s", "x_c_{}_%s", "x_inf_{}_%s"))

    phi_gamma_p = [
        Implies(q_mapping[ineq],
                eliminate_inequality_atom_real(ineq, real_vars1, real_vars2, d, d_c, d_inf,
                                            rho[i], sigma[i], t_rho[i], t_sigma[i]))
        for i, ineq in enumerate(real_ineqs)
    ] + [
        Implies(q_mapping[eq],
                eliminate_equality_atom_real(eq, real_vars1, real_vars2, d, d_c, d_inf))
        for eq in real_eqs
    ]

    # Non-triviality constraint
    non_trivial_dc = Or(NotEquals(dc_i, Real(0)) for dc_i in d_c)
    theta_r = non_trivial_dc

    theta = And(theta_r, theta_i)
    # Statics
    x_r = fresh_real_vector("x_r{}%s", len(real_vars1))
    x_i = fresh_int_vector("x_i{}%s", len(int_vars1))
    int_constant_mapping = dict(list(zip(int_vars1, x_i)) + list(zip(int_vars2, x_i)))
    real_constant_mapping = dict(list(zip(real_vars1, x_r)) + list(zip(real_vars2, x_r)))

    phi_delta = And([Implies(q_mapping[atom], atom) for atom in int_ineqs + int_eqs]).substitute(int_constant_mapping)
    phi_gamma = And([Implies(q_mapping[atom], atom) for atom in real_ineqs + real_eqs]).substitute(real_constant_mapping)

    phi_xi_int_finite = []
    phi_xi_real_finite = []
    phi_Xi = []

    # Iterate over the stored pairs, which is a robust way to link the components.
    for int_bridge_var, real_bridge_var in bridge_pairs:
        # The `mapping` dictionary directly links original vars to their new components.
        int_mapping = mapping[int_bridge_var]
        real_mapping = mapping[real_bridge_var]

        (v1_i, v2_i), (w1_i, w2_i) = int_mapping
        (v1_r, v2_r), (w1_r, w2_r) = real_mapping

        # Now, find the indices.
        idx_v1_i = int_vars1.index(v1_i)
        idx_w2_i = int_vars2.index(w2_i)

        idx_v1_r = real_vars1.index(v1_r)
        idx_w2_r = real_vars2.index(w2_r)

        phi_Xi.append(eliminate_bridge_atom(
            v1_dc=d_c[idx_v1_r],
            v2_dc=d_c[idx_w2_r],
            v1_a=a[idx_v1_i],
            v1_dinf=d_inf[idx_v1_r],
            w2_a=a[idx_w2_i],
            w2_dinf=d_inf[idx_w2_r],
            v1_a0=a0[idx_v1_i],
            w2_a0=a0[idx_w2_i],
            v1_d0=d[idx_v1_r],
            w2_d0=d[idx_w2_r],
        ))




    selector = FreshSymbol(typ.INT, "sel%s")
    selector_restriction = Or(Equals(selector, Int(i)) for i in [0, 1, 2])

    phi_pppp = And(skel, theta, selector_restriction,
        Implies(NotEquals(selector, Int(0)), And(phi_gamma_p)),
        Implies(NotEquals(selector, Int(1)), And(phi_delta_p)),
        Implies(Equals(selector, Int(0)), phi_gamma),
        Implies(Equals(selector, Int(1)), phi_delta),
        Implies(Equals(selector, Int(0)), And(phi_xi_real_finite)),
        Implies(Equals(selector, Int(1)), And(phi_xi_int_finite)),
        Implies(Equals(selector, Int(2)), And(phi_Xi)),
    )

    all_fresh_vars = list(qs) + list(x_i) + list(x_r) + list(a) + list(a0) + list(omega) + list(p) + list(d) + list(d_c) + list(d_inf) + list(sigma) + list(rho) + list(t_rho) + list(t_sigma) + [selector]
    return Exists(all_fresh_vars, phi_pppp)

def full_ramsey_elimination_mixed(formula: ExtendedFNode) -> ExtendedFNode:
    """Performs full mixed Ramsey quantifier elimination (with optional existential elimination)."""
    assert formula.is_ramsey()
    f = make_mixed_input_format(formula)

    # Handle nested existentials before Ramsey elimination
    if f.arg(0).is_exists():
        f, _ = eliminate_existential_quantifier(f)

    return eliminate_ramsey_mixed(f)


