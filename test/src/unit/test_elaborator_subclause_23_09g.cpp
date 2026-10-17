// Tests for the §23.9 scope rules as they reach the type a variable of a scope
// within a module is declared with. A generate block (§27.5), a task, a
// function and a begin-end block are each a scope, and a typedef one of them
// declares (§6.18) stands over the module's of the same name for the
// variables it declares, deciding the built-in methods (§6.16, §23.7) and the
// class (§8.5) a select through such a variable reaches.

#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(LocalTypedefScope, GenerateBlockTypedefTypesItsOwnVariables) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int v;\n"
      "endclass\n"
      "module m;\n"
      "  typedef int t;\n"
      "  typedef int h_t;\n"
      "  if (1) begin : g\n"
      "    typedef string t;\n"
      "    typedef C h_t;\n"
      "    t s;\n"
      "    h_t h;\n"
      "    int n, k;\n"
      "    initial n = s.len();\n"
      "    initial k = h.nope;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "'len' is not a built-in method", 13, "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'C' has no member named 'nope'", 14, "8.5"));
}

TEST(LocalTypedefScope, FunctionTypedefTypesItsOwnVariables) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int v;\n"
      "endclass\n"
      "module m;\n"
      "  typedef int t;\n"
      "  typedef int h_t;\n"
      "  function int f();\n"
      "    typedef string t;\n"
      "    typedef C h_t;\n"
      "    t s;\n"
      "    h_t h;\n"
      "    return s.len() + h.nope;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "'len' is not a built-in method", 12, "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'C' has no member named 'nope'", 12, "8.5"));
}

// A scope that declares no typedef of the name sees the module's: a block's
// variable of the module's `int t` is an integral value, which has no
// built-in method.
TEST(LocalTypedefScope, BlockWithoutItsOwnTypedefReadsTheModules) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int t;\n"
      "  if (1) begin : g\n"
      "    t v;\n"
      "    int n;\n"
      "    initial n = v.len();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'len' is not a built-in method of the integral or real value 'v'", 6,
      "23.7"));
}

}  // namespace
