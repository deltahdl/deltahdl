#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(ContinuousAssignDeclElaboration, NetDeclAssignCreatesContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].name, "w");
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_NE(mod->assigns[0].rhs, nullptr);
}

TEST(ContinuousAssignDeclElaboration, NetDeclAssignLhsIsNetName) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire mynet = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns[0];
  ASSERT_NE(ca.lhs, nullptr);
  EXPECT_EQ(ca.lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ca.lhs->text, "mynet");
}

TEST(ContinuousAssignDeclElaboration, NetDeclAssignWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire [7:0] data = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].width, 8u);
}

TEST(ContinuousAssignDeclElaboration, NetDeclNoInitNoContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->assigns.size(), 0u);
}

TEST(ContinuousAssignDeclElaboration, MultiNetDeclAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire a = 1'b0, b = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 2u);
}

TEST(ContinuousAssignDeclElaboration, TriNetDeclAssignCreatesContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  tri w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_NE(mod->assigns[0].rhs, nullptr);
}

TEST(ContinuousAssignDeclElaboration, StrengthNetDeclAssignCreatesContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic en;\n"
      "  wire (strong1, pull0) mynet = en;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_NE(mod->assigns[0].rhs, nullptr);
}

TEST(ContinuousAssignDeclElaboration, NetDeclAssignConflictsWithProcAssign) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire w = 1'b0;\n"
      "  initial w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "has both continuous and procedural assignments", 2,
                            "6.5"));
}

TEST(ContinuousAssignDeclElaboration, InterconnectNetDeclAssignIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  interconnect sig = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "an interconnect net cannot be given a value where it is declared", 2,
      "10.3.1"));
}

TEST(ContinuousAssignDeclElaboration, InterconnectNetDeclNoAssignIsOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  interconnect sig;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ContinuousAssignDeclElaboration, InterconnectVectorNetDeclAssignIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  interconnect [3:0] sig = 4'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "an interconnect net cannot be given a value where it is declared", 2,
      "10.3.1"));
}

}  // namespace
