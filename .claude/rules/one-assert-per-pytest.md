# One assertion per Python test, and what counts as one

Write exactly one assertion in a Python test, because a check in CI counts them and fails on any other number. `assert-one-assert-per-pytest` runs over `test/lib/python/` and `test/scripts/` as the job of the same name in `.github/workflows/scripts.yml`, counts the assertions in each test function, and fails the job on any function that does not have exactly one.

A `with pytest.raises(...)` block is one of them. It asserts that the code inside it raises, so the checker counts it exactly as it counts an `assert` statement. A test that wraps a call in `pytest.raises` and then asserts on what the call left behind therefore counts two, and the job reports it as:

```text
Found: …/test_concurrent_walk.py:187:test_a_failed_walk_…:2
```

The path, the line, and the function name are followed by the count. The trailing `2` is how many assertions were found, not a column.

## What tripping it costs

Tripping this check costs the run, and it leaves the test results standing. `assert-one-assert-per-pytest` fails, and a failed job fails the run whatever else passed. No job in `.github/workflows/scripts.yml` declares `needs: assert-one-assert-per-pytest`, so every per-package pytest job runs alongside it and reports whether the tests in the change pass. Read `gh run view --log-failed` to tell an assertion count this check rejected from a test that broke.

## Splitting a two-claim test

Give each claim its own test, named for the claim it makes. A test that raises and then inspects is making two. One of the new tests keeps the `pytest.raises` block and claims that the failure surfaces. The other has to reach the state the failure left behind, which means letting the failure past. Put the `contextlib.suppress` that lets it past into a helper rather than into the test body, so that the single assertion in the body is the only thing there a reader could take for one:

```python
def _walk_past_the_failure(lrm: Path, output: Path) -> None:
    """Run the walk whose last call raises and absorb the raise."""
    with contextlib.suppress(RuntimeError):
        _walk(lrm, output, "8", _one_fails)
```

Put the builder or input that produces the failure at module level once both tests need it, rather than defining it twice inside the two bodies.

## Where it bites

Nothing about the shape of the source warns you. Files across the tree use `pytest.raises`, and every one of them is fine, because none pairs it with a second assertion in the same body. A new test is the only place the pairing appears. So the check to make before a push is not "does this file use `pytest.raises`" but "does any one test body both raise and assert".
