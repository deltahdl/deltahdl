// Tests for the §23.9 scope rules as they reach the type a variable of a scope
// within a module is declared with. A generate block (§27.5), a task, a
// function and a begin-end block are each a scope, and a typedef one of them
// declares (§6.18) stands over the module's of the same name for the
// variables it declares, deciding the built-in methods (§6.16, §23.7) and the
// class (§8.5) a select through such a variable reaches.

#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_module.h"

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

// An interface's typedef is a name of the interface's scope, never of a module
// connected to it, so a module's function formal written with the module's own
// class `t` is a handle of that class whatever array typedef `t` the interface
// declares, and takes none of the typedef's dimensions.
TEST(LocalTypedefScope, InterfacesArrayTypedefLeavesAModulesClassFormal) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(
      "interface ifc;\n"
      "  typedef int t [2];\n"
      "endinterface\n"
      "module m (ifc p);\n"
      "  class t;\n"
      "    int v;\n"
      "  endclass\n"
      "  function automatic int g(t h);\n"
      "    return h.v;\n"
      "  endfunction\n"
      "endmodule\n"
      "module top;\n"
      "  ifc i ();\n"
      "  m u (i);\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  const RtlirModule* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->function_decls.size(), 1u);
  EXPECT_TRUE(m->function_decls[0]->func_args[0].unpacked_dims.empty());
}

}  // namespace
