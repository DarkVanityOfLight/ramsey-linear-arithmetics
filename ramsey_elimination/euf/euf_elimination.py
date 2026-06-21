from typing import Tuple
from itertools import combinations

from ramsey_extensions.fnode import ExtendedFNode
from formula_utils import _fresh_vector, collect_atoms, fresh_bool_vector
from simplifications import make_euf_input_format
from .existential_elimination import eliminate_existential_quantifier
FNode = ExtendedFNode

from pysmt.shortcuts import NotEquals, Or, And, Implies, Exists



def eliminate_ramsey_euf(qFormula: ExtendedFNode) -> ExtendedFNode:
    assert qFormula.is_ramsey()


    eqs, _, _ = collect_atoms(qFormula)
    skeleton_vars = fresh_bool_vector("s_{}_%s", len(eqs))

    skeleton = And([Implies(skeleton_vars[i], eqs[i]) for i in range(len(eqs))])

    qargs: Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]] = qFormula.quantifier_vars() #type: ignore
    n = len(qargs[0])
    T = qargs[0][0].get_type()

    vecs = [_fresh_vector("x_{}_%s", n, T) for _ in range(4)]

    uneq = And([Or([NotEquals(x, y) for (x, y) in zip(xs, ys)]) for (xs, ys) in combinations(vecs, 2)])

    formals = qargs[0] + qargs[1]

    clique = And([
        skeleton.substitute(dict(zip(formals, xs_p + ys_p)))
        for xs_p, ys_p in combinations(vecs, 2)
    ])

    return Exists(skeleton_vars + [x for vec in vecs for x in vec], And(uneq, clique))


def full_ramsey_elimination_euf(formula: ExtendedFNode) -> ExtendedFNode:
    """Performs full EUF Ramsey quantifier elimination (with optional existential elimination)."""
    assert formula.is_ramsey()
    f = make_euf_input_format(formula)

    # Handle nested existentials before Ramsey elimination
    if formula.arg(0).is_exists():
        f = eliminate_existential_quantifier(f)

    return eliminate_ramsey_euf(f)

    

