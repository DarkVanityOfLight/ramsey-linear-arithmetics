
import sys
from pathlib import Path

from pysmt.shortcuts import is_sat

sys.path.append(str(Path(__file__).parent.parent))

from typing import Dict, List, Tuple
from ramsey_elimination.formula_utils import int_vector, real_vector

from ramsey_extensions.shortcuts import Plus, Times, Int, Real, And, Ramsey, LT, GT, GE, ToReal, Or, Minus 


# LIRA Benchmarks 
# -----------------------------------------------------------------

def benchmark_geometric_divergence_convergence(dim_i: int, dim_r: int):
    xi = int_vector("xi", dim_i)
    yi = int_vector("yi", dim_i)
    xr = real_vector("xr", dim_r)
    yr = real_vector("yr", dim_r)
    x = xi + xr
    y = yi + yr

    # Integer part must at least double: y_i >= 2*x_i + 1
    int_conds = [GE(yi[j], Plus(Times(Int(2), xi[j]), Int(1))) for j in range(dim_i)]
    # Real part must more than halve: x_r > 2*y_r
    real_conds = [GT(xr[j], Times(Real(2), yr[j])) for j in range(dim_r)]

    formula = And(And(int_conds), And(real_conds))
    return Ramsey(x, y, formula)

def benchmark_bounded_int_jump(dim_i: int, dim_r: int, bound: int = 10):
    xi = int_vector("xi", dim_i)
    yi = int_vector("yi", dim_i)
    xr = real_vector("xr", dim_r)
    yr = real_vector("yr", dim_r)
    x = xi + xr
    y = yi + yr

    # Real part is strictly increasing
    real_increase = [LT(xr[j], yr[j]) for j in range(dim_r)]
    # Integer jump is determined by the first real component's value
    int_jump_lower = GT(ToReal(yi[0]), Plus(ToReal(xi[0]), xr[0]))
    # Integer jump is bounded by a constant
    int_jump_upper = LT(yi[0], Plus(xi[0], Int(bound)))

    formula = And(And(real_increase), int_jump_lower, int_jump_upper)
    return Ramsey(x, y, formula)

def benchmark_independent_growth(dim_i: int, dim_r: int):
    xi = int_vector("xi", dim_i)
    yi = int_vector("yi", dim_i)
    xr = real_vector("xr", dim_r)
    yr = real_vector("yr", dim_r)
    x = xi + xr
    y = yi + yr

    int_conds = [LT(Plus(xi[j], Int(1)), yi[j]) for j in range(dim_i)]
    real_conds = [LT(Plus(xr[j], Real(1)), yr[j]) for j in range(dim_r)]

    formula = And(int_conds + real_conds)
    return Ramsey(x, y, formula)

def benchmark_oscillating_int_steady_real(dim_i: int, dim_r: int):
    xi = int_vector("xi", dim_i)
    yi = int_vector("yi", dim_i)
    xr = real_vector("xr", dim_r)
    yr = real_vector("yr", dim_r)
    x = xi + xr
    y = yi + yr

    real_increase = [GT(Minus(yr[j], xr[j]), Real(1)) for j in range(dim_r)]
    # (x_i > 0 and y_i < 0) or (x_i < 0 and y_i > 0)
    int_oscillate = Or(
        And(GT(xi[0], Int(0)), LT(yi[0], Int(0))),
        And(LT(xi[0], Int(0)), GT(yi[0], Int(0)))
    )

    formula = And(And(real_increase), int_oscillate)
    return Ramsey(x, y, formula)

def benchmark_shrinking_interval(dim_i: int, dim_r: int):
    xi = int_vector("xi", dim_i)
    yi = int_vector("yi", dim_i)
    # xr is the lower bound, xz is the upper bound
    xr = real_vector("xr", dim_r)
    yr = real_vector("yr", dim_r)
    xz = real_vector("xz", dim_r)
    yz = real_vector("yz", dim_r)
    x = xi + xr + xz
    y = yi + yr + yz

    # Interval is shrinking: 2 * (new_len) < old_len
    interval_shrink = [
        LT(Times(Real(2), Minus(yz[j], yr[j])), Minus(xz[j], xr[j]))
        for j in range(dim_r)
    ]
    # Integer is trapped inside the first interval
    int_trapped = And(LT(xr[0], ToReal(xi[0])), LT(ToReal(xi[0]), xz[0]))
    # Keep bounds moving correctly
    bounds_progress = [And(LT(xr[j], yr[j]), GT(xz[j], yz[j])) for j in range(dim_r)]

    formula = And(And(interval_shrink), int_trapped, And(bounds_progress))
    return Ramsey(x, y, formula)

def benchmark_int_grows_faster_than_real(dim_i: int, dim_r: int):
    xi = int_vector("xi", dim_i)
    yi = int_vector("yi", dim_i)
    xr = real_vector("xr", dim_r)
    yr = real_vector("yr", dim_r)
    x = xi + xr
    y = yi + yr

    real_increase = [LT(xr[j], yr[j]) for j in range(dim_r)]
    int_increase = [LT(xi[j], yi[j]) for j in range(dim_i)]

    sum_int_diff = Plus([Minus(yi[j], xi[j]) for j in range(dim_i)])
    sum_real_diff = Plus([Minus(yr[j], xr[j]) for j in range(dim_r)])
    faster_growth = GT(ToReal(sum_int_diff), sum_real_diff)

    formula = And(And(real_increase), And(int_increase), faster_growth)
    return Ramsey(x, y, formula)

def benchmark_lia_core_unsat(dim_i: int, dim_r: int, bound: int = 5):
    xi = int_vector("xi", dim_i)
    yi = int_vector("yi", dim_i)
    xr = real_vector("xr", dim_r)
    yr = real_vector("yr", dim_r)
    x = xi + xr
    y = yi + yr

    # Integer part is strictly increasing
    int_increase = [LT(xi[j], yi[j]) for j in range(dim_i)]
    # The sum of jumps across all integer dimensions is bounded
    sum_int_diff = Plus([Minus(yi[j], xi[j]) for j in range(dim_i)])
    int_bound = LT(sum_int_diff, Int(bound))
    # Distractor: Real part increases more than the integer part
    real_distractor = [GT(Minus(yr[j], xr[j]), ToReal(sum_int_diff)) for j in range(dim_r)]

    formula = And(And(int_increase), int_bound, And(real_distractor))
    return Ramsey(x, y, formula)

def benchmark_cauchy_real_divergent_int(dim_i: int, dim_r: int):
    xi = int_vector("xi", dim_i)
    yi = int_vector("yi", dim_i)
    xr = real_vector("xr", dim_r)
    yr = real_vector("yr", dim_r)
    x = xi + xr
    y = yi + yr

    int_increase = [LT(xi[j], yi[j]) for j in range(dim_i)]
    # x_r > 2*y_r implies a decreasing sequence that converges to 0
    real_cauchy = [GT(xr[j], Times(Real(2), yr[j])) for j in range(dim_r)]

    formula = And(And(int_increase), And(real_cauchy))
    return Ramsey(x, y, formula)

if __name__ == '__main__':

    from ramsey_extensions.environment import push_ramsey
    from ramsey_elimination.alternative_mixed_elimination import full_ramsey_elimination_mixed
    from pysmt.shortcuts import is_sat

    push_ramsey()
    # --- Example Usage ---
    dim_i = 1
    dim_r = 1

    benchmarks = {
        "Bench 1: Geometric Div/Conv": (benchmark_geometric_divergence_convergence, (dim_i, dim_r)),
        "Bench 2: Bounded Int Jump (Unsat)": (benchmark_bounded_int_jump, (dim_i, dim_r)),
        "Bench 3: Independent Growth": (benchmark_independent_growth, (dim_i, dim_r)),
        "Bench 4: Oscillating Int": (benchmark_oscillating_int_steady_real, (dim_i, dim_r)),
        "Bench 5: Shrinking Interval (Unsat)": (benchmark_shrinking_interval, (dim_i, dim_r)),
        "Bench 6: Int Grows Faster": (benchmark_int_grows_faster_than_real, (dim_i, dim_r)),
        "Bench 7: LIA Core Unsat": (benchmark_lia_core_unsat, (dim_i, dim_r)),
        "Bench 8: Cauchy Real": (benchmark_cauchy_real_divergent_int, (dim_i, dim_r)),
    }

    for name, (func, args) in benchmarks.items():
        print(f"--- {name} ---")
        formula_obj = func(*args)
        r = full_ramsey_elimination_mixed(formula_obj)
        print(r.serialize())
        is_sat(r)
        print("-" * (len(name) + 6), "\n")
