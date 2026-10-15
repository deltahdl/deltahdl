#include <gtest/gtest.h>

#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_config_params.h"
#include "helpers_reported_error.h"

namespace {

// §33.4.3 bars a generate scope from a hierarchical reference in a config
// override, and §27.6 makes an unnamed generate block one, named genblk<n>, so
// a reference through `genblk1` is reported as one through a named block is.
TEST(ConfigParamOverride, HierRefThroughUnnamedGenerateBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module adder #(parameter W = 8); endmodule\n"
      "module top;\n"
      "  if (1) begin\n"
      "    localparam X = 5;\n"
      "  end\n"
      "  adder a1();\n"
      "endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.genblk1.X));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' override of parameter 'W' uses a "
                            "hierarchical reference that passes through a "
                            "generate scope",
                            10, "33.4.3"));
}

// The parameter named `name` of `m`, or null.
const RtlirParamDecl* ParamNamed(const RtlirModule* m, std::string_view name) {
  for (const auto& p : m->params) {
    if (p.name == name) return &p;
  }
  return nullptr;
}

// §33.4.3: a config may give a real parameter a real value, which reaches the
// instance as an instantiation's real assignment would.
TEST(ConfigParamApply, RealOverrideReachesTheInstance) {
  ElabFixture f;
  auto* u =
      ConfigElabFirstChild(f,
                           "module c #(parameter real R = 1.0); endmodule\n"
                           "module top; c u(); endmodule\n"
                           "config cfg;\n"
                           "  design top;\n"
                           "  instance top.u use #(.R(2.5));\n"
                           "endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirParamDecl* r = ParamNamed(u, "R");
  ASSERT_NE(r, nullptr);
  EXPECT_DOUBLE_EQ(r->resolved_real, 2.5);
}

// §33.4.3: an override naming nothing that holds a constant cannot be applied,
// and is reported rather than leaving the parameter at its default unsaid.
TEST(ConfigParamApply, OverrideNamingNoConstantReported) {
  ElabFixture f;
  ConfigElab(f,
             "module adder #(parameter W = 8); endmodule\n"
             "module top; adder a1(); endmodule\n"
             "config cfg;\n"
             "  design top;\n"
             "  instance top.a1 use #(.W(NOPE));\n"
             "endconfig\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "configuration override of parameter 'W' of "
                            "'adder' has no constant value",
                            5, "33.4.3"));
}

// §33.4.3: names in an override resolve upward from the instance's parent as a
// bind statement's do, so top.WIDTH reaches past the parent a1 to top: b's W
// is 7.
TEST(ConfigParamApply, OverrideReadsAParameterAboveTheParent) {
  ElabFixture f;
  auto* design =
      ConfigElab(f,
                 "module leaf #(parameter W = 1); endmodule\n"
                 "module mid; leaf b(); endmodule\n"
                 "module top; parameter WIDTH = 7; mid a1(); endmodule\n"
                 "config cfg;\n"
                 "  design top;\n"
                 "  instance top.a1.b use #(.W(top.WIDTH));\n"
                 "endconfig\n");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* b =
      design->top_modules[0]->children[0].resolved->children[0].resolved;
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(ResolvedParam(b, "W"), 7);
}

// §33.4.3 with §3.12.1: the top-level module's enclosing scope is its
// compilation unit, so an override of the top reads a parameter declared
// there.
TEST(ConfigParamApply, TopOverrideReadsACompilationUnitParameter) {
  ElabFixture f;
  auto* design = ConfigElab(f,
                            "parameter CU_P = 5;\n"
                            "module top; parameter WIDTH = 1; endmodule\n"
                            "config cfg;\n"
                            "  design top;\n"
                            "  instance top use #(.WIDTH(CU_P));\n"
                            "endconfig\n");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design->top_modules[0], "WIDTH"), 5);
}

// §33.4.3: a bare name a config localparam declares is that localparam, so a
// defparam changing a parameter of the instance's parent, which refolds the
// child's overrides, leaves W at the localparam's 24.
TEST(ConfigParamApply, DefparamRefoldKeepsTheConfigLocalparam) {
  ElabFixture f;
  auto* design =
      ConfigElab(f,
                 "module adder #(parameter W = 8); endmodule\n"
                 "module top4; parameter S = 16, Q = 1; adder a1(); endmodule\n"
                 "module test; top4 t(); defparam t.Q = 2; endmodule\n"
                 "config cfg;\n"
                 "  localparam S = 24;\n"
                 "  design test;\n"
                 "  instance test.t.a1 use #(.W(S + 0));\n"
                 "endconfig\n");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* a1 =
      design->top_modules[0]->children[0].resolved->children[0].resolved;
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(ResolvedParam(a1, "W"), 24);
}

}  // namespace
