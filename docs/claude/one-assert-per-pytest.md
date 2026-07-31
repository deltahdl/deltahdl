# One assertion per Python test, and what counts as one

`assert-one-assert-per-pytest` runs over `test/lib/python/` and
`test/scripts/` in the `static-analysis` job. It counts the assertions in
each test function and fails the job on any function that does not have
exactly one.

A `with pytest.raises(...)` block is one of them. It asserts that the code
inside it raises, so the checker counts it exactly as it counts an
`assert` statement. A test that wraps a call in `pytest.raises` and then
asserts on what the call left behind therefore counts two, and the job
reports it as:

```text
Found: …/test_concurrent_walk.py:187:test_a_failed_walk_…:2
```

The path, the line, and the function name are followed by the count. The
trailing `2` is how many assertions were found, not a column.

## The cost of tripping it

`static-analysis` runs before the per-package pytest jobs and gates them.
When it fails, every pytest job reports `skipped`, so a push that trips
this check does not merely fail — it reports nothing at all about whether
the tests in the change pass. A green pytest job is the only evidence the
change works, and a run that trips this check produces none.

## Splitting a two-claim test

A test that raises and then inspects is making two claims, and each wants
a test that says so in its name. One keeps the `pytest.raises` block and
claims that the failure surfaces. The other has to reach the state the
failure left behind, which means letting the failure past — put the
`contextlib.suppress` that does so in a helper rather than in the test
body, so the single assertion in the body is the only thing there that
could be read as one:

```python
def _walk_past_the_failure(lrm: Path, output: Path) -> None:
    """Run the walk whose last call raises and absorb the raise."""
    with contextlib.suppress(RuntimeError):
        _walk(lrm, output, "8", _one_fails)
```

The builder or input that produces the failure belongs at module level
once both tests need it, rather than being defined twice inside the two
bodies.

## Where it bites

Nothing about the shape of the source warns you. Files across the tree
use `pytest.raises`, and every one of them is fine, because none pairs it
with a second assertion in the same body. A new test is the only place
the pairing appears, so the check to make before a push is not "does this
file use `pytest.raises`" but "does any one test body both raise and
assert".
