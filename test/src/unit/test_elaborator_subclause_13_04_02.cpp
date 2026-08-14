#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  // The report names no subclause: elaborator_validate_funcbody.cpp:172 passes
  // Subclause::None(), since §6.8 permits a run-time initial value and neither
  // §6.21 nor §13.4.2 narrows that for a static variable inside a subroutine.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static variable 's' initializer must be a "
                            "constant expression",
                            3, ""));
}

// §13.4.2: "Automatic function items cannot be accessed by hierarchical
// references." A path into an automatic function's local is rejected, and the
// report names §13.4.2 rather than §13.3.1, which states the same sentence for
// a task and is a different rule about a different construct.
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
  const Diagnostic* diag =
      FindDiag(f, "hierarchical reference to object in automatic function");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "13.4.2");
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
  const Diagnostic* diag =
      FindDiag(f, "hierarchical reference to object in automatic function");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "13.4.2");
}

}  // namespace
