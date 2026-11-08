#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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
