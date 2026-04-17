#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(DefparamElaboration, OverridesDefaultValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter WIDTH = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.WIDTH = 16;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* child = design->top_modules[0]->children[0].resolved;
  EXPECT_EQ(child->params[0].resolved_value, 16);
  EXPECT_TRUE(child->params[0].is_resolved);
}

TEST(DefparamElaboration, NotFoundWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter WIDTH = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.BOGUS = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(DefparamElaboration, MultipleAssignmentsInOneStatement) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child #(parameter int A = 1, parameter int B = 2);\n"
      "endmodule\n"
      "module m;\n"
      "  child u1();\n"
      "  defparam u1.A = 10, u1.B = 20;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules[0]->children.empty());
}

TEST(DefparamElaboration, MultiLevelHierarchicalPath) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf #(parameter int X = 1)();\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf u_leaf();\n"
      "endmodule\n"
      "module top;\n"
      "  mid u_mid();\n"
      "  defparam u_mid.u_leaf.X = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mid = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(mid, nullptr);
  ASSERT_FALSE(mid->children.empty());
  auto* leaf = mid->children[0].resolved;
  ASSERT_NE(leaf, nullptr);
  ASSERT_FALSE(leaf->params.empty());
  EXPECT_EQ(leaf->params[0].resolved_value, 42);
  EXPECT_TRUE(leaf->params[0].is_resolved);
}

TEST(DefparamElaboration, LastDefparamWinsForSameParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  defparam u.P = 10;\n"
      "  defparam u.P = 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->params[0].resolved_value, 20);
}

TEST(DefparamElaboration, RhsCanReferenceParameterInSameModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 0)();\n"
      "endmodule\n"
      "module top;\n"
      "  parameter int NEW_VALUE = 42;\n"
      "  child u();\n"
      "  defparam u.P = NEW_VALUE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->params[0].resolved_value, 42);
}

TEST(DefparamElaboration, RhsRejectsNonConstantExpression) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int P = 0)();\n"
      "endmodule\n"
      "module top;\n"
      "  logic [3:0] data;\n"
      "  child u();\n"
      "  defparam u.P = data;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors || f.diag.WarningCount() > 0);
}

TEST(DefparamElaboration, DefparamInGenerateBlockCannotEscapeScope) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 5)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  if (1) begin : g\n"
      "    defparam u.P = 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  EXPECT_NE(u->params[0].resolved_value, 99);
}

}  // namespace
