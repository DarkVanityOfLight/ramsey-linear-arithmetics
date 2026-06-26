from typing import List

from ramsey_extensions.fnode import ExtendedFNode
from ramsey_elimination.formula_utils import _fresh_vector
from ramsey_extensions.shortcuts import Exists, Xor, Ramsey, is_sat
from ramsey_elimination.eliminate_ramsey import eliminate_ramsey



def is_mondec(f: ExtendedFNode):
    
    free_vars: List[ExtendedFNode] = list(f.get_free_variables())
    T = free_vars[0].get_type()

    # Trivial case: 0 or 1 variable -> always decomposable
    if len(free_vars) < 2:
        return True

    # TODO: Probs start from 1
    for j in range(len(free_vars)):
        x, y = _fresh_vector("x_{}_%s", j, T), _fresh_vector("y_{}_%s", j, T)
        z = _fresh_vector("z_{}_%s", len(free_vars)-j, T)

        m1 = dict(zip(free_vars, (x + z)))
        m2 = dict(zip(free_vars, (y + z)))
        fp = Ramsey(x, y, Exists(z, Xor(f.substitute(m1), f.substitute(m2))))

        fr = eliminate_ramsey(fp)

        if is_sat(fr):
            return False
    return True
