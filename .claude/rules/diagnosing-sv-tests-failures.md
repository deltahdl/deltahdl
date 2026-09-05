# Diagnosing sv-tests failures

To root-cause a failing sv-tests file, run the binary on that file rather than reasoning about the failure from the source alone. On 2026-07-01 reading the code produced two confident hypotheses in a row — scalar-versus-queue dispatch, then concat-init-not-lowered — and both were wrong. The actual causes only became visible from the binary's own output. `print_reason` in `scripts/run_sv_tests/__init__.py` says the same thing in its docstring, which is why the runner prints the tool's output under every FAIL line.

Read the CI log before building, because that printing means a file rejected by the simulator is already diagnosed there. What the log drops is the rest of a simulated run's stdout: `check_assertions` keeps the first `:assert:` line that did not hold and discards every other line the run printed. That gap is the case this file is about, and it is the whole of what [verifying-through-ci](verifying-through-ci.md) allows building for.

Fetch the file with:

```sh
gh api repos/chipsalliance/sv-tests/contents/tests/chapter-N/<path>.sv \
  --jq .content | base64 -d
```

Then run it from an isolated Debug build directory; `ninja src/deltahdl` rebuilds incrementally. A file passes when each `:assert:` line reports equal values. Verify the fix by pushing, not by rebuilding.
