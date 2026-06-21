from typing import List, cast, Tuple
from ramsey_extensions.formula import ExtendedFNode

from formula_utils import skolemize
from ramsey_extensions.shortcuts import Ramsey

def eliminate_existential_quantifier(formula: ExtendedFNode) -> ExtendedFNode:
    assert formula.is_ramsey()

    # If there's no existential quantifier, return unchanged
    if not formula.arg(0).is_exists():
        return formula

    ex_vars: List[ExtendedFNode] = list(formula.arg(0).quantifier_vars())
    subformula = formula.arg(0).arg(0)

    sk = skolemize(subformula, set(ex_vars), ex_vars[0].get_type())

    x_vars, y_vars = cast(Tuple[Tuple[ExtendedFNode, ...], Tuple[ExtendedFNode, ...]], formula.quantifier_vars())
    return Ramsey(list(x_vars), list(y_vars), sk)
