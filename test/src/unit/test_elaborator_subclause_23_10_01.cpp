#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam right-hand side shall be a constant "
                            "expression involving only numbers and references "
                            "to parameters",
                            6, "23.10.1"));
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

TEST(DefparamElaboration, RhsRejectsHierarchicalReference) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int P = 0)();\n"
      "endmodule\n"
      "module other;\n"
      "  parameter int OUT = 100;\n"
      "endmodule\n"
      "module top;\n"
      "  other o();\n"
      "  child u();\n"
      "  defparam u.P = o.OUT;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam right-hand side may only reference "
                            "parameters declared in the same module",
                            9, "23.10.1"));
}

TEST(DefparamElaboration, DefparamInGenerateCannotTargetSiblingScope) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 5) ();\n"
      "endmodule\n"
      "module top;\n"
      "  if (1) begin : g1\n"
      "    child u();\n"
      "  end\n"
      "  if (1) begin : g2\n"
      "    defparam g1.u.P = 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  bool saw_99 = false;
  for (auto& c : design->top_modules[0]->children) {
    if (c.resolved != nullptr) {
      for (auto& p : c.resolved->params) {
        if (p.name == "P" && p.resolved_value == 99) saw_99 = true;
      }
    }
  }
  EXPECT_FALSE(saw_99);
}

TEST(DefparamElaboration, DefparamCannotTargetOtherArrayInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 5) ();\n"
      "endmodule\n"
      "module top;\n"
      "  child u [1:0] ();\n"
      "  defparam u[0].P = 77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  int count_77 = 0;
  for (auto& c : design->top_modules[0]->children) {
    if (c.resolved != nullptr) {
      for (auto& p : c.resolved->params) {
        if (p.name == "P" && p.resolved_value == 77) ++count_77;
      }
    }
  }
  EXPECT_LE(count_77, 1);
}

// §23.10.1: defparam overrides value parameters; a localparam is local and
// cannot be redefined by a defparam statement.
TEST(DefparamElaboration, CannotOverrideLocalparam) {
  ElabFixture f;
  Elaborate(
      "module child ();\n"
      "  localparam int L = 1;\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  defparam u.L = 5;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam cannot override a local parameter", 6,
                            "23.10.1"));
}

// §23.10.1: the report that refuses a defparam aimed at a localparam names the
// subclause stating the rule, so a caller learns which rule was enforced
// without matching the wording of the message.
TEST(DefparamElaboration, CannotOverrideLocalparamNames23_10_1) {
  ElabFixture f;
  Elaborate(
      "module child ();\n"
      "  localparam int L = 1;\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  defparam u.L = 5;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam cannot override a local parameter", 6,
                            "23.10.1"));
}

// §23.10.1's defparam reaches a parameter through Elaborator::ApplyDefparams,
// which writes RtlirParamDecl directly and shares no code with the instance
// assignment of §23.10.2, so the characters §6.16 forbids truncating have to be
// asserted on this path separately. "configured" is ten characters, past the
// eight resolved_value holds. The declaration's own default is five, so a
// defparam that replaced the number without replacing the characters leaves
// "unset" here.
TEST(DefparamElaboration, ReplacesEveryCharacterOfAStringParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  parameter string NAME = \"unset\";\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  defparam u.NAME = \"configured\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  ASSERT_EQ(u->params.size(), 1u);
  EXPECT_EQ(u->params[0].name, "NAME");
  EXPECT_TRUE(u->params[0].is_string_value);
  EXPECT_EQ(u->params[0].resolved_string, "configured");
}

}  // namespace
