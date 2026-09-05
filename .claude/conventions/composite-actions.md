# Composite actions over shell scripts

Write a CI mechanism as a composite action, not as a shell script. The house pattern is `.github/actions/<name>/action.yml` with `using: composite` and alphabetical keys, as in the sibling repository at `~/Git/10U-Labs/10ulabs.com`. `install-llvm` and `install-gcc` exist here.

A job uses the action and then has a small `run:` step for ccache, pip or pmd, since a `uses:` step cannot also `run:`.

See [unpinned-ci-toolchain](../memories/unpinned-ci-toolchain.md) for the change that occasioned the pattern, and for the shell-script attempt the user rejected.
