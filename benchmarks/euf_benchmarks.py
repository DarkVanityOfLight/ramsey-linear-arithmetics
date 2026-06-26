"""EUF workloads for the Ramsey elimination backend.
"""

from pysmt.shortcuts import And, Equals, Exists, Function, FunctionType, Not, Symbol, Type

from ramsey_elimination.euf.euf_elimination import full_ramsey_elimination_euf
from ramsey_extensions.shortcuts import Ramsey


ELIMINATION_FUNC = full_ramsey_elimination_euf

BENCHMARK_ARGS = {
    "benchmark_pairwise_distinct": [(4,), (16,), (64,)],
    "benchmark_coordinate_equality": [(4,), (16,), (64,)],
    "benchmark_same_function_image": [(4,), (16,), (64,)],
    "benchmark_same_composed_image": [(4, 1), (16, 2), (64, 3)],
    "benchmark_distinct_function_images": [(4,), (16,), (64,)],
    "benchmark_collapsed_distinct_function_images": [(4,), (16,), (64,)],
    "benchmark_fixed_points": [(4,), (16,), (64,)],
    "benchmark_congruence_conflict": [(4,), (16,), (64,)],
    "benchmark_existential_witness": [(4,), (16,), (64,)],
}

EXPECTED_SATISFIABILITY = {
    "benchmark_pairwise_distinct": True,
    "benchmark_same_function_image": True,
    "benchmark_same_composed_image": True,
    "benchmark_distinct_function_images": True,
    "benchmark_collapsed_distinct_function_images": True,
    "benchmark_fixed_points": True,
    "benchmark_coordinate_equality": False,
    "benchmark_congruence_conflict": False,
    "benchmark_existential_witness": False,
}


def _symbols(dim: int):
    """Create Ramsey vectors and unary function symbols over a fresh sort."""
    if dim < 1:
        raise ValueError("dimension must be positive")

    sort = Type("U")
    x = [Symbol(f"x_{index}", sort) for index in range(dim)]
    y = [Symbol(f"y_{index}", sort) for index in range(dim)]
    f = Symbol("f", FunctionType(sort, [sort]))
    g = Symbol("g", FunctionType(sort, [sort]))
    return sort, x, y, f, g


def benchmark_pairwise_distinct(dim: int):
    _, x, y, _, _ = _symbols(dim)
    return Ramsey(x, y, And([Not(Equals(left, right)) for left, right in zip(x, y)]))


def benchmark_coordinate_equality(dim: int):
    _, x, y, _, _ = _symbols(dim)
    return Ramsey(x, y, And([Equals(left, right) for left, right in zip(x, y)]))


def benchmark_same_function_image(dim: int):
    _, x, y, f, _ = _symbols(dim)
    return Ramsey(x, y, And([
        Equals(Function(f, [left]), Function(f, [right]))
        for left, right in zip(x, y)
    ]))


def benchmark_same_composed_image(dim: int, depth: int):
    if depth < 1:
        raise ValueError("depth must be positive")

    _, x, y, f, g = _symbols(dim)
    x_terms = list(x)
    y_terms = list(y)
    for index in range(depth):
        function = f if index % 2 == 0 else g
        x_terms = [Function(function, [term]) for term in x_terms]
        y_terms = [Function(function, [term]) for term in y_terms]
    return Ramsey(x, y, And([
        Equals(left, right) for left, right in zip(x_terms, y_terms)
    ]))


def benchmark_distinct_function_images(dim: int):
    _, x, y, f, _ = _symbols(dim)
    return Ramsey(x, y, And([
        Not(Equals(Function(f, [left]), Function(f, [right])))
        for left, right in zip(x, y)
    ]))


def benchmark_collapsed_distinct_function_images(dim: int):
    _, x, y, f, g = _symbols(dim)
    constraints = []
    for left, right in zip(x, y):
        f_left = Function(f, [left])
        f_right = Function(f, [right])
        constraints.extend((
            Not(Equals(f_left, f_right)),
            Equals(Function(g, [f_left]), Function(g, [f_right])),
        ))
    return Ramsey(x, y, And(constraints))


def benchmark_fixed_points(dim: int):
    _, x, y, f, _ = _symbols(dim)
    constraints = []
    for left, right in zip(x, y):
        constraints.extend((
            Equals(Function(f, [left]), left),
            Equals(Function(f, [right]), right),
        ))
    return Ramsey(x, y, And(constraints))


def benchmark_congruence_conflict(dim: int):
    _, x, y, f, g = _symbols(dim)
    constraints = []
    for left, right in zip(x, y):
        constraints.extend((
            Equals(Function(f, [left]), Function(f, [right])),
            Not(Equals(Function(g, [Function(f, [left])]), Function(g, [Function(f, [right])]))),
        ))
    return Ramsey(x, y, And(constraints))


def benchmark_existential_witness(dim: int):
    sort, x, y, f, _ = _symbols(dim)
    witnesses = [Symbol(f"w_{index}", sort) for index in range(dim)]
    body = And([
        And(Equals(witness, Function(f, [source])), Equals(witness, target))
        for source, target, witness in zip(x, y, witnesses)
    ])
    return Ramsey(x, y, Exists(witnesses, body))
