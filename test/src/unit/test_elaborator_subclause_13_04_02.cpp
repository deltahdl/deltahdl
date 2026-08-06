#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(FunctionLifetimeElaboration, DefaultLifetimeFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int adder(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionLifetimeElaboration, RecursiveAutomaticFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int factorial(int n);\n"
      "    if (n <= 1) return 1;\n"
      "    return n * factorial(n - 1);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionLifetimeElaboration, StaticVarNonConstantInitializerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function automatic int bad_init(int x);\n"
      "    static int s = x;\n"
      "    return s;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.2: the items of an automatic function are allocated per call, so they
// cannot be reached through a hierarchical reference. A path into an automatic
// function's local is rejected.
TEST(FunctionLifetimeElaboration, AutoFunctionItemHierRefInContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  function automatic int g();\n"
      "    int x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  assign y = g.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// Contrast: a static function allocates its items statically, so the same
// hierarchical path is permitted and the §13.4.2 restriction must not fire.
TEST(FunctionLifetimeElaboration, StaticFunctionItemHierRefAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  function static int g();\n"
      "    int x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  assign y = g.x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The restriction also applies to references from within procedural blocks.
TEST(FunctionLifetimeElaboration, AutoFunctionItemHierRefInInitialError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  function automatic int g();\n"
      "    int x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  initial y = g.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
