---
name: include-what-you-use
description: "Every file includes the header that declares each symbol it uses and no header it uses nothing from; an umbrella header that only forwards other headers is not wanted, and a linter finding about includes fails the job rather than printing a warning."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 9f933e93-a52c-49aa-ae9f-934899f85199
  modified: 2026-09-19T00:18:10.759Z
---

# Include what you use

A translation unit or header names the header that declares each symbol it uses, and names no header it uses nothing from. A header that declares nothing of its own and exists to pull other headers in is not wanted: `parser/ast.h`, `simulator/sva_engine.h` and `simulator/vpi.h` were three such and were dissolved on 2026-09-18. The one exception is `vpi_user.h`'s include of `vpi_compatibility.h`: Annex L.1 has `vpi_user.h` include that file and forbids an application including it directly, so that include carries an `IWYU pragma: export`. `vpi_user.h` itself was an umbrella over ten sub-headers until 2026-09-18 and is now the one C file Annex K.2 prints, about 1,000 lines, exempted by name from the 950-line gate for that reason; the simulator's own `VpiContext`, `VpiObject` and model helpers are internal headers a file includes directly.

**Why:** On 2026-09-18 the user saw the `assert-no-dead-includes` step print 2,731 "no header providing X is directly included" warnings for a tree whose umbrella headers were exempted from the check by configuration, and said that implicit includes are bad programming, hard to debug, and that what clang-tidy complains about should be done, and that a finding should fail the job rather than be a warning. The exemption had also hidden real dead includes: `<string>` and `<cstdint>` were on its ignore list, so an unused include of either was invisible.

**How to apply:** `misc-include-cleaner` runs whole in `etc/clang_tidy/src.yml` and `test_src_unit.yml` with no `IgnoreHeaders`, under `-warnings-as-errors`, and the `clang-include-cleaner-headers` job in deltahdl.yml runs the same analysis on every header, because the check judges only the translation unit it is given. Fix a finding by adding or removing the include it names, never by widening an ignore list or adding an umbrella. Do not add a `using namespace` to a header to make it self-contained unless the headers around it already do; qualify the name instead. See [lrm-source-of-truth](lrm-source-of-truth.md) for why the VPI files are the exception.
