---
name: include-what-you-use
description: "Every file includes the header that declares each symbol it uses and no header it uses nothing from; an umbrella header that only forwards other headers is not wanted, and a linter finding about includes fails the job rather than printing a warning."
metadata: 
  node_type: memory
  type: feedback
---

# Include what you use

A translation unit or header names the header that declares each symbol it uses, and names no header it uses nothing from. A header that declares nothing of its own and exists to pull other headers in is not wanted. The one exception is `vpi_user.h`'s include of `vpi_compatibility.h`: the source Annex K.2 prints has `vpi_user.h` include that file (printed page 1319), and Annex L.1 draws the consequence that an application is not to include it directly; the include stands in the file as the annex prints it, with no pragma, and a translation unit that selects a compatibility mode reaches the renaming macros through `vpi_user.h` alone. `vpi_user.h` itself is the one C file Annex K.2 prints, about 1,000 lines, exempted by name from the 950-line gate for that reason; the simulator's own `VpiContext`, `VpiObject` and model helpers are internal headers a file includes directly.

**Why:** Implicit includes are bad programming and hard to debug, and what clang-tidy reports about them is to be done, so a finding fails the job rather than printing a warning. An exemption or ignore list hides real dead includes along with the rest: a header on the list can be included unused and nothing says so.

**How to apply:** `misc-include-cleaner` runs whole in `etc/clang_tidy/src.yml` and `test_src_unit.yml` with no `IgnoreHeaders`, under `-warnings-as-errors`, and the `clang-include-cleaner-headers` job in deltahdl.yml runs the same analysis on every header, because the check judges only the translation unit it is given. Fix a finding by adding or removing the include it names, never by widening an ignore list or adding an umbrella. Do not add a `using namespace` to a header to make it self-contained unless the headers around it already do; qualify the name instead. See [lrm-source-of-truth](lrm-source-of-truth.md) for why the VPI files are the exception.
