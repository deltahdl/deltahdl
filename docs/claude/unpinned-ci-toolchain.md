# The unpinned CI toolchain

Nothing in CI is pinned; everything floats to latest. The decision was made on 2026-06-23, prompted by clang-format resolving to v19 in CI while the local install was v22. It landed on `main` in commits `240075952`, `b77615a7b` and `d95a32ef0`.

What floats: runner images (`ubuntu-24.04` to `ubuntu-latest`, `macos-26` to `macos-latest`, on `runs-on:` lines only — the job and artifact name strings such as `build-ubuntu-24-04-x86-64-clang` are identifiers that `needs:` and artifact references depend on, and stay as labels). LLVM, clang, clang-tidy, clang-format, llvm-cov, llvm-profdata, g++ and gcc are no longer version-suffixed. PMD resolves its latest release through the GitHub API into a step output with a dynamic cache key.

The mechanism is composite actions, not shell scripts. The first attempt used raw `scripts/ci/*.sh` and the user rejected it. The house pattern is `.github/actions/<name>/action.yml` with `using: composite` and alphabetical keys, as in the sibling repository at `~/Git/10U-Labs/10ulabs.com`. `install-llvm` and `install-gcc` exist here. A job uses the action and then has a small `run:` step for ccache, pip or pmd, since a `uses:` step cannot also `run:`.

One trap is worth remembering. The unversioned apt.llvm.org repository — `deb http://apt.llvm.org/<codename>/ llvm-toolchain-<codename> main` — is trunk, not stable, so picking the highest available clang selected 23, an unreleased development build. Trunk makes the formatting gate unwinnable, because nightly output drifts and cannot be reproduced off the runner, and it destabilises clang-tidy. The fix in `b77615a7b` queries `api.github.com/repos/llvm/llvm-project/releases/latest`, derives the major version, and adds the stable branch repository `llvm-toolchain-<codename>-<major> main`. That still follows releases automatically while staying reproducible.

GitHub Actions tags stay at their major version (`@v5`, `@v4`). Floating within a major is the safe mechanism; unpinning to a moving ref is a supply-chain risk. This was flagged to the user and deliberately left pinned.
