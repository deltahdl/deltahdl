// Tests for the §23.9 scope rules as they reach a subroutine no module holds:
// one declared in the compilation-unit scope (§3.12.1) and one declared in a
// package (Clause 26). §23.9 lists a task and a function among the elements
// that define a scope and searches an identifier referenced without a
// hierarchical path upward from the scope it stands in, and neither of these
// bodies stands in a module -- so the walk that resolves a module's
// subroutines never reached them, and a read of a name nothing declares was
// accepted there. Every case here writes the read in one of the two bodies and
// says whether §23.9 finds a declaration for it.
//
// The cases over a module's subroutines and procedural blocks are in
// test_elaborator_subclause_23_09a.cpp, and those over generate blocks in
// test_elaborator_subclause_23_09b.cpp.

#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §23.9 with §3.12.1: a function at compilation-unit scope reading a name
// declared nowhere. Line 3 is the read; the module beside it declares nothing
// of the name either, so the module is not what answers. The read stands on an
// assignment's right side because that is the position the collector reads
// (CollectProcRhsIdents); a return's expression is #4358's.
TEST(UnitScopeSubroutineReads, UndeclaredNameInAUnitFunctionIsReported) {
  ElabFixture f;
  ElabOk(
      "function int f();\n"
      "  int x;\n"
      "  x = undeclared;\n"
      "  return x;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'undeclared'",
                            3, "23.9"));
}

// The same read inside a randsequence production code block of the function,
// the shape of sv-tests' §18.17 `_fail` files: the code block is a statement
// of the body, reached through the same walk. Line 5 is the code block.
TEST(UnitScopeSubroutineReads,
     UndeclaredNameInAUnitFunctionsProductionCodeBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "function int f();\n"
      "  int x;\n"
      "  randsequence( main )\n"
      "    main : first;\n"
      "    first : { x = undeclared; };\n"
      "  endsequence\n"
      "  return x;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'undeclared'",
                            5, "23.9"));
}

// §23.9 with Clause 26: a function declared in a package reading a name
// declared nowhere, on line 4.
TEST(UnitScopeSubroutineReads, UndeclaredNameInAPackageFunctionIsReported) {
  ElabFixture f;
  ElabOk(
      "package p;\n"
      "  function int f();\n"
      "    int x;\n"
      "    x = undeclared;\n"
      "    return x;\n"
      "  endfunction\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'undeclared'",
                            4, "23.9"));
}

// The control for the compilation-unit body: each name it reads is one §23.9
// lets it reach -- a variable and a parameter of the compilation unit, a
// member of an enumeration declared there (§6.19 makes it a constant of the
// scope), a name a package the unit imports provides (§26.3), and a name an
// import written in the body itself provides. The names are distinct so that
// a predicate missing any one of them is what fails this case, and the read
// stands on an assignment's right side, the position the collector reads, so
// that the case is not satisfied by a read never collected.
TEST(UnitScopeSubroutineReads, AUnitFunctionReadingReachableNamesIsClean) {
  EXPECT_TRUE(
      ElabOk("package q;\n"
             "  int from_q = 4;\n"
             "endpackage\n"
             "package r;\n"
             "  int from_r = 5;\n"
             "endpackage\n"
             "import q::*;\n"
             "int unit_var = 1;\n"
             "parameter int unit_param = 2;\n"
             "typedef enum { UNIT_MEMBER = 3 } unit_e;\n"
             "function int f();\n"
             "  import r::from_r;\n"
             "  int x;\n"
             "  x = unit_var + unit_param + UNIT_MEMBER + from_q + from_r;\n"
             "  return x;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

// The control for the package body: its own variable and parameter, a member
// of an enumeration it declares, and a name another package provides through
// an import written in the package (§26.3).
TEST(UnitScopeSubroutineReads, APackageFunctionReadingReachableNamesIsClean) {
  EXPECT_TRUE(
      ElabOk("package q;\n"
             "  int from_q = 4;\n"
             "endpackage\n"
             "package p;\n"
             "  import q::*;\n"
             "  int pkg_var = 1;\n"
             "  parameter int pkg_param = 2;\n"
             "  typedef enum { PKG_MEMBER = 3 } pkg_e;\n"
             "  function int f();\n"
             "    int x;\n"
             "    x = pkg_var + pkg_param + PKG_MEMBER + from_q;\n"
             "    return x;\n"
             "  endfunction\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

// The body's own names are not the compilation unit's to declare: a formal and
// a local of the function answer their reads, as they do in a module's
// function (CollectSubroutineLocalNames).
TEST(UnitScopeSubroutineReads, AUnitFunctionReadingItsOwnNamesIsClean) {
  EXPECT_TRUE(
      ElabOk("function int f(int formal);\n"
             "  int local_var = 1;\n"
             "  int x;\n"
             "  x = formal + local_var;\n"
             "  return x;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
