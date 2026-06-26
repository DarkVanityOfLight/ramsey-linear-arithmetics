from benchmarks import euf_benchmarks
from pysmt.shortcuts import is_sat


def test_euf_benchmark_configuration_covers_every_benchmark():
    configured = set(euf_benchmarks.BENCHMARK_ARGS)
    discovered = {
        name for name in dir(euf_benchmarks)
        if name.startswith("benchmark_") and callable(getattr(euf_benchmarks, name))
    }
    assert configured == discovered
    assert set(euf_benchmarks.EXPECTED_SATISFIABILITY) == configured


def test_euf_benchmarks_construct_ramsey_formulas():
    for name, arg_sets in euf_benchmarks.BENCHMARK_ARGS.items():
        for args in arg_sets:
            formula = getattr(euf_benchmarks, name)(*args)
            assert formula.is_ramsey()


def test_euf_benchmarks_eliminate_with_the_configured_backend():
    for name, arg_sets in euf_benchmarks.BENCHMARK_ARGS.items():
        for args in arg_sets:
            formula = getattr(euf_benchmarks, name)(*args)
            result = euf_benchmarks.ELIMINATION_FUNC(formula)
            assert not result.is_ramsey()


def test_euf_benchmarks_have_the_expected_satisfiability():
    for name, arg_sets in euf_benchmarks.BENCHMARK_ARGS.items():
        for args in arg_sets:
            formula = getattr(euf_benchmarks, name)(*args)
            result = euf_benchmarks.ELIMINATION_FUNC(formula)
            assert is_sat(result) is euf_benchmarks.EXPECTED_SATISFIABILITY[name]
