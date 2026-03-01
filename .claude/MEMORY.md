# Claude Code Memory

## Testing philosophy
- User does TDD: write failing tests FIRST, then implement
- Tests must catch real-world failures, not just echo back existing data
- The battery of tests must be EXHAUSTIVE, no happy-path-only testing
- When testing data-driven matching (like _PREFIX_PATTERNS), test against actual values from the codebase, not just the values already in the pattern list
- Write integration tests that scan the real codebase to verify assumptions
- 100% branch coverage is necessary but NOT sufficient — data bugs slip through

## Pipeline design principles
- NEVER silently continue after failure — fail fast, fail loud
- NEVER buffer subprocess output — stream everything to the terminal in real time
- NEVER use capture_output=True between pipeline stages (classify_files → classify_file → classify_test)
- Every successful side effect (commit, push, issue close) must print confirmation

## classify_files/classify_file/classify_test scripts
- Located in `scripts/classify_files/`, `scripts/classify_file/`, `scripts/classify_test/`
- Tests in `test/scripts/classify_files/`, `test/scripts/classify_file/`, `test/scripts/classify_test/`
- Each has unit/, integration/, e2e/ test directories
- CI checks: pylint 10/10, mypy clean, 100% branch coverage, jscpd 0 clones, one-assert-per-pytest
- Verification commands pattern:
  - `PYTHONPATH=.:scripts python -m pytest test/scripts/<pkg>/ -v`
  - `PYTHONPATH=.:scripts python -m pytest test/scripts/<pkg>/unit/ --cov=<pkg> --cov-branch --cov-fail-under=100`
  - `PYTHONPATH=. python3 -m pylint scripts/<pkg>/`
  - `PYTHONPATH=.:scripts:test/scripts/<pkg>/unit python3 -m pylint --recursive=y test/scripts/<pkg>/`
  - `PYTHONPATH=. python3 -m mypy scripts/<pkg>/`
  - `jscpd --pattern "**/*.py" --threshold 0 --reporters console scripts/<pkg>/`
  - `jscpd --pattern "**/*.py" --threshold 0 --reporters console test/scripts/<pkg>/`
  - `assert-one-assert-per-pytest --verbose test/scripts/<pkg>/`

## Commit conventions
- Classification commits: `Classify <TestName> → §<clause> [skip ci]`
- Infrastructure commits: NO [skip ci] unless user explicitly says so
- Always ask/confirm before adding [skip ci]
