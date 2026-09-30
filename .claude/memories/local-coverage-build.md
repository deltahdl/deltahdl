---
name: local-coverage-build
description: "Locating the exact lines assert-coverage leaves uncovered in one file needs a local instrumented build; DELTAHDL_COVERAGE=ON links with lld, which the Mac does not have, so the flags are passed by hand."
metadata:
  node_type: memory
  type: reference
  originSessionId: ef682c43-8cab-4c9d-8a68-d98c1351a7e5
  modified: 2026-09-30T08:54:19.204Z
---

# A local coverage build to find uncovered lines

The assert-coverage log in `.github/workflows/deltahdl.yml` gives per-file counts only, and its HTML report is published only when the run passes, so the lines a change left uncovered are found locally.

`-DDELTAHDL_COVERAGE=ON` adds `-fuse-ld=lld` (CMakeLists.txt), and the Mac's Command Line Tools clang has no lld, so the link fails. Configure a scratch build directory with coverage off and the instrumentation passed directly:

```sh
cmake -S . -B <scratch>/covbuild -DDELTAHDL_COVERAGE=OFF -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_CXX_FLAGS="-fprofile-instr-generate -fcoverage-mapping" \
  -DCMAKE_EXE_LINKER_FLAGS="-fprofile-instr-generate" \
  -DCMAKE_SHARED_LINKER_FLAGS="-fprofile-instr-generate"
cmake --build <scratch>/covbuild --target deltahdl -j 12
LLVM_PROFILE_FILE=<scratch>/prof/%p.profraw <scratch>/covbuild/src/deltahdl design.sv
xcrun llvm-profdata merge -sparse <scratch>/prof/*.profraw -o m.profdata
xcrun llvm-cov show <scratch>/covbuild/src/deltahdl -instr-profile=m.profdata src/<file>.cpp
```

Look for missed regions rather than missed lines. The CI job's current LLVM counts a line as missed when a region with a count of zero starts on it, while the Mac's older llvm-cov gives that line the count of the covered region it continues. An untaken operand of `||` on a line of its own is one example. The Mac then reports no missed line where CI reports one. List the regions with a count of zero from `xcrun llvm-cov export … src/<file>.cpp`, where the fifth field of each region is its count. A unit test binary built in the same directory (`--target test_<name>`) gives the unit tests' share.

This is an investigation, which [[verifying-through-ci]] allows; the gate itself is still read from the run.
