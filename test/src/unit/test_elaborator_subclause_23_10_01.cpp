#include <string_view>

#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"

using namespace delta;

namespace {

// The module instantiated as `inst_name` directly under `parent`, or nullptr
// when `parent` instantiates nothing by that name. The elaborator flattens a
// generate block into the names of what it holds, so an instance written as
// `u` inside `begin : b` at genvar value 0 is instantiated as `b_0_u`, and a
// case reading children by position cannot say which block instance it got.
RtlirModule* ChildInstantiatedAs(RtlirModule* parent,
                                 std::string_view inst_name) {
  for (auto& child : parent->children) {
    if (child.inst_name == inst_name) return child.resolved;
  }
  return nullptr;
}

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
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "defparam target not found",
                              5, "23.10.1"));
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

// §23.10.1: "a defparam statement in a hierarchy in or under a generate block
// instance (see Clause 27) or an array of instances shall not change a
// parameter value outside that hierarchy." `u` is instantiated by `top` and
// not by block `g`, so the statement inside `g` is refused and `P` keeps the
// value its own declaration gave it.
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
  EXPECT_EQ(u->params[0].resolved_value, 5);
  EXPECT_TRUE(u->params[0].is_resolved);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam in a generate block shall not change a "
                            "parameter value outside that block",
                            6, "23.10.1"));
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

// §23.10.1: "Each instantiation of a generate block is considered to be a
// separate hierarchy scope", so a statement standing in `g2` reaches only what
// `g2` holds. The elaborator flattens `g1`'s contents to `g1_u`, and `g1.u`
// therefore names nothing `g2` can reach: the containment rule leaves the
// statement with no target rather than letting it cross into the sibling.
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
  auto* u = ChildInstantiatedAs(design->top_modules[0], "g1_u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->params[0].resolved_value, 5);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "defparam target not found",
                              8, "23.10.1"));
}

// §23.10.1 bars a defparam in a generate block from changing a parameter
// "outside that hierarchy" and bars nothing inside it, so a statement whose
// target is instantiated by the block that holds it takes effect.
TEST(DefparamElaboration, AppliesInsideTheGenerateBlockThatHoldsIt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 5)();\n"
      "endmodule\n"
      "module top;\n"
      "  if (1) begin : g\n"
      "    child u();\n"
      "    defparam u.P = 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  auto* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->params[0].resolved_value, 99);
  EXPECT_TRUE(u->params[0].is_resolved);
}

// §23.10.1: "Each instantiation of a generate block is considered to be a
// separate hierarchy scope", so every iteration of the loop applies its own
// statement to its own instance. The clause's example writes the genvar on the
// right-hand side -- `defparam somename[i+1].my_flop.xyz = i ;` -- which is why
// the two instances are asserted to hold different values.
TEST(DefparamElaboration, AppliesOncePerLoopGenerateBlockInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 5)();\n"
      "endmodule\n"
      "module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : b\n"
      "    child u();\n"
      "    defparam u.P = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->children.size(), 2u);
  auto* first = ChildInstantiatedAs(design->top_modules[0], "b_0_u");
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->params[0].resolved_value, 0);
  auto* second = ChildInstantiatedAs(design->top_modules[0], "b_1_u");
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second->params[0].resolved_value, 1);
}

// §23.10.1 reads on the generate block instance a statement stands in, and an
// else arm §27.5 selected is a block instance like any other, so the statement
// it holds reaches the instance beside it.
TEST(DefparamElaboration, AppliesInsideAnElseGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 5)();\n"
      "endmodule\n"
      "module top;\n"
      "  if (0) begin : g1\n"
      "    child u();\n"
      "  end else begin : g2\n"
      "    child u();\n"
      "    defparam u.P = 77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u = ChildInstantiatedAs(design->top_modules[0], "g2_u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->params[0].resolved_value, 77);
  EXPECT_TRUE(u->params[0].is_resolved);
}

// The alternative a case generate selects is a generate block instance too, so
// §23.10.1 lets the statement it holds reach what that alternative
// instantiated.
TEST(DefparamElaboration, AppliesInsideAGenerateCaseAlternative) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 5)();\n"
      "endmodule\n"
      "module top;\n"
      "  parameter int SEL = 1;\n"
      "  case (SEL)\n"
      "    0: begin : g0\n"
      "      child u();\n"
      "    end\n"
      "    1: begin : g1\n"
      "      child u();\n"
      "      defparam u.P = 33;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u = ChildInstantiatedAs(design->top_modules[0], "g1_u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->params[0].resolved_value, 33);
  EXPECT_TRUE(u->params[0].is_resolved);
}

// §27.5 instantiates the alternative the condition selects and no other, so a
// defparam in the arm that was not selected is nowhere in the elaborated
// design: it changes nothing, and there is nothing for it to be reported
// about. That is why a zero count of warnings is the claim here.
TEST(DefparamElaboration, IsNotAppliedFromAnUnselectedAlternative) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 5)();\n"
      "endmodule\n"
      "module top;\n"
      "  if (0) begin : g1\n"
      "    child u();\n"
      "    defparam u.P = 99;\n"
      "  end else begin : g2\n"
      "    child u();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  auto* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->params[0].resolved_value, 5);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// A target that names nothing anywhere breaches no rule of §23.10.1: there is
// no parameter outside the block for the statement to change, so it stays the
// warning a target that was not found draws outside a generate block.
TEST(DefparamElaboration, TargetMissingInsideAGenerateBlockWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  if (1) begin : g\n"
      "    defparam nosuch.P = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "defparam target not found",
                              3, "23.10.1"));
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
