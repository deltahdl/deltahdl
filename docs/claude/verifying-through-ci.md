# Verifying through CI, not locally

The rule, as the user restated it on 2026-06-29: never build or test
locally unless local is inevitable. It is a condition, not a ban with an
exception. CI is the default; local build and test is permitted, with no
separate sign-off, the moment a fix is genuinely un-crackable through CI
iteration. Do not over-ask — when local is inevitable, say so and proceed.

Inevitable means runtime-invisible bugs in coroutines, the scheduler or
event watchers, where every code path reads correctly; commits `27fd32124`
and `2ba1794f1` were cracked locally after about eleven wasted CI rounds.
It also covers full-pipeline output mismatches such as sv-tests failures.
A deterministic lowering, elaborator or evaluation fix is never inevitable
no matter how much regression risk it carries.

The rule is binary, not a trade-off. Two justifications were used and
corrected. "Protect a CI cycle" is not one: CI runs on free GitHub
compute, in parallel, and there is no scarce resource to protect. "Local
caught a regression, so it was worth it" is not one either: if the fix was
not un-crackable, CI would have surfaced the same diff for free.

When local is warranted, use an isolated build directory — for example
`build-seqdebug/`, Ninja and Debug and clang++ — never the pre-existing
`build/`. Instrument with prints, strip all debug output and run
clang-format before committing, and remove the directory afterwards. Note
that `git stash -u` sweeps an untracked build directory into the stash;
use plain `git stash` for before-and-after baselines.

This covers the Python side too. The `scripts/` and `lib/python/` gates —
pytest, the coverage gates, pylint, `mypy --strict`,
`assert-one-assert-per-pytest`, jscpd — all run in
`.github/workflows/scripts.yml` for free. As the user put it: "CI does all
checks. doing things locally costs Claude tokens. CI is free."

The origin of the rule was 2026-06-21, when the documented block on local
builds was rationalised as possibly stale, the user's own `build/` was
reconfigured to get `std::jthread` compiling, full builds were run and
test binaries executed to verify ordinary fixes. The lesson is not that
local is forbidden — it is that going local for routine work CI can verify,
and touching the user's own build directory, are both wrong.

Verify by reading CI: `gh run view`, `gh run list`, and
`gh api repos/deltahdl/deltahdl/actions/jobs/<id>/logs`.
