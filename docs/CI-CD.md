# CI/CD Pipeline

DeltaHDL uses a single GitHub Actions workflow (`.github/workflows/ci.yml`)
with four parallel jobs. All tools are open source.

## Workflow: `.github/workflows/ci.yml`

Triggers on push to `main` and on all pull requests.

```
ci.yml
├── lint          clang-format, clang-tidy, cppcheck, Lizard
├── build         CMake matrix (GCC 14 + Clang 18, Debug + Release), tests
├── coverage      llvm-cov instrumentation, Codecov upload
└── sanitizers    ASan + UBSan build, tests
```

## Job 1: lint

Static analysis and code constraint enforcement.

| Step | Tool | Purpose |
|------|------|---------|
| Format check | `clang-format --dry-run --Werror --style='{...}'` | Enforce formatting via inline style |
| Static analysis | `clang-tidy --config='{...}'` | Code constraints + bug detection via inline config |
| Bug detection | `cppcheck --enable=all` | Supplementary static analysis |
| File limits | `lizard -l cpp` + `wc -l` | Lines-per-file constraint |

### Code Constraint Enforcement

The ENGINE.md §9 constraints are enforced automatically in CI:

| Constraint | Limit | Tool | Configuration |
|------------|-------|------|---------------|
| Nesting depth | ≤ 3 | clang-tidy `readability-function-size` | `NestingThreshold: 3` |
| Arguments per function | ≤ 5 | clang-tidy `readability-function-size` | `ParameterThreshold: 5` |
| Statements per function | ≤ 50 | clang-tidy `readability-function-size` | `StatementThreshold: 50` |
| Lines per file | ≤ 800 | Lizard + shell `wc -l` check | `lizard -l cpp -T nloc=800` |
| Cognitive complexity | ≤ 15 | clang-tidy `readability-function-cognitive-complexity` | `Threshold: 15` |

The cognitive complexity threshold is a proxy for the "Big-O optimized" constraint —
functions with high cognitive complexity tend to have unnecessarily complex control
flow that correlates with suboptimal algorithmic choices.

## Job 2: build

Matrix build across compilers and build types.

| Axis | Values |
|------|--------|
| Compiler | GCC 14, Clang 18 |
| Build type | Debug, Release |
| OS | Ubuntu 24.04 |

Steps:
1. Configure with CMake (`-DCMAKE_BUILD_TYPE=<type>`)
2. Build the `deltahdl` binary and test binaries
3. Run unit tests via CTest
4. Run integration tests (simulate test `.sv` files)

## Job 3: coverage

Source-based code coverage using LLVM tools.

| Tool | Purpose |
|------|---------|
| `clang++ -fprofile-instr-generate -fcoverage-mapping` | Instrument build |
| `llvm-profdata merge` | Merge raw profile data |
| `llvm-cov export --format=lcov` | Generate line + branch coverage report |
| Codecov upload | Track coverage over time |

### Why llvm-cov over gcov+lcov

- Better C++23 coroutine support (LLVM D82928 fix for coroutine frame coverage)
- Source-based coverage mapping (more accurate than debug-info-based gcov)
- Line AND branch coverage in a single tool
- Faster report generation on large codebases

Steps:
1. Build with Clang + coverage flags
2. Run all tests (unit + integration)
3. Merge `.profraw` files with `llvm-profdata merge`
4. Export lcov-format report with `llvm-cov export`
5. Upload to Codecov

## Job 4: sanitizers

Runtime error detection using Clang sanitizers.

| Sanitizer | Detects |
|-----------|---------|
| AddressSanitizer (ASan) | Buffer overflows, use-after-free, memory leaks |
| UndefinedBehaviorSanitizer (UBSan) | Signed overflow, null deref, alignment, shift |

Steps:
1. Build with Clang + `-fsanitize=address,undefined`
2. Run all tests
3. Fail the job on any sanitizer finding

## Configuration

All tool configuration is inline in `.github/workflows/ci.yml`. There are no
separate `.clang-format` or `.clang-tidy` config files — everything is passed
explicitly on the command line so CI is the single source of truth.

## Adding New Checks

To add a clang-tidy check: edit the `--config='{...}'` block in the
`Run clang-tidy` step of `ci.yml`. To adjust a threshold: modify the
corresponding `CheckOptions` entry in that same block.

To add a new CI job: add a new job to `.github/workflows/ci.yml` under the
`jobs:` key. Keep it parallel with existing jobs unless it depends on their
outputs.
