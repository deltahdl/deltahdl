#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_param_value.h"
#include "helpers_reported_error.h"

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
// `g2` holds. `g1.u` is a name §23.6 defines and the design holds, and it is
// outside `g2`, so the statement is refused rather than merely left with
// nothing to bind to. This asserted the "target not found" warning while the
// path could not be read at all: the elaborator compared `g1` against the
// flattened instance name `g1_u`, so a statement reaching a real sibling and
// one naming nothing produced the same report.
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam in a generate block shall not change a "
                            "parameter value outside that block",
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
// cannot be redefined by a defparam statement. The third argument to
// ReportedError is the other half of the claim: the report names the subclause
// stating the rule, so a caller learns which rule was enforced without matching
// the wording of the message.
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

// §23.10.1 lets a defparam change a parameter "in any module, interface, or
// program instance throughout the design using the hierarchical name of the
// parameter", and §27.5 makes a named generate block one of the names such a
// path is built from: "if the generate block selected for instantiation is
// named, then this name declares a generate block instance and is the name for
// the scope it creates. Normal rules for hierarchical naming apply." Its
// Example 1 writes the gate instantiated inside a block named u1 as
// `test.u1.g1`, so `g.u.P` names the child's parameter and the override lands.
//
// The design records that child as `g_u`, so comparing the written `g` against
// an instance name found nothing and the override was dropped with a warning.
TEST(DefparamElaboration,
     ReachesAParameterInsideANamedConditionalGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 5)();\n"
      "endmodule\n"
      "module top;\n"
      "  if (1) begin : g\n"
      "    child u();\n"
      "  end\n"
      "  defparam g.u.P = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u = ChildInstantiatedAs(design->top_modules[0], "g_u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->params[0].resolved_value, 99);
  EXPECT_TRUE(u->params[0].is_resolved);
}

// The same source, asserting that nothing is reported as unresolved. Separate
// from the value because the two can disagree: Elaborator::ApplyDefparamSite
// and Elaborator::ReportUnresolvedDefparamSite decide independently, off one
// applied-set key, so a path that resolves and sets the value while the key is
// never inserted would warn about an override that landed.
TEST(DefparamElaboration, NamedGenerateBlockPathReportsNoUnresolvedTarget) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int P = 5)();\n"
      "endmodule\n"
      "module top;\n"
      "  if (1) begin : g\n"
      "    child u();\n"
      "  end\n"
      "  defparam g.u.P = 99;\n"
      "endmodule\n",
      f);
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_EQ(d.message.find("defparam target not found"), std::string::npos)
        << "the path named a parameter, so nothing is left unresolved";
  }
}

// §27.4: a named loop generate block "is a declaration of an array of generate
// block instances", whose "index values in this array are the values assumed by
// the genvar during elaboration", and §27.4 writes the resulting hierarchical
// names as `B1[0].B2[0].B3[0].N3`. So `b[1]` selects the second block instance
// and `b[1].u.P` names the parameter in it alone.
//
// Index 1 rather than 0, because an implementation that discards the select and
// takes the first block instance answers index 0 correctly. Asserting the other
// instance keeps its default is the other half of that: without it a change
// applying the override to every instance would pass.
TEST(DefparamElaboration, ReachesAParameterInOneIterationOfALoopGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 5)();\n"
      "endmodule\n"
      "module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : b\n"
      "    child u();\n"
      "  end\n"
      "  defparam b[1].u.P = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* first = ChildInstantiatedAs(design->top_modules[0], "b_0_u");
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->params[0].resolved_value, 5);
  auto* second = ChildInstantiatedAs(design->top_modules[0], "b_1_u");
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second->params[0].resolved_value, 99);
}

// §23.6 makes each node of a hierarchical name "a separate scope with respect
// to identifiers", so the `u` inside block instance `b[0]` and the `u` declared
// beside the block are two objects and `b[0].u.P` names the first.
//
// This is the half of the defect that wrote the wrong parameter rather than
// none. The select was dropped while the path was being read, leaving the
// components `u` and `P`, which resolved against the enclosing module and
// overrode the instance the source never named. The two do not collide in
// declared_names_, which holds `u` and `b_0_u`, so nothing reported it.
TEST(DefparamElaboration,
     LoopGenerateBlockIndexDoesNotSelectAModuleLevelSibling) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 5)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : b\n"
      "    child u();\n"
      "  end\n"
      "  defparam b[0].u.P = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* sibling = ChildInstantiatedAs(design->top_modules[0], "u");
  ASSERT_NE(sibling, nullptr);
  EXPECT_EQ(sibling->params[0].resolved_value, 5);
  auto* inside = ChildInstantiatedAs(design->top_modules[0], "b_0_u");
  ASSERT_NE(inside, nullptr);
  EXPECT_EQ(inside->params[0].resolved_value, 99);
}

// §27.6 gives every unnamed generate block the name genblk<n>, and §23.6 still
// refuses a path written outside it: objects declared in one "can be referenced
// by hierarchical names only from within the block and within any hierarchy
// instantiated by the block". So `u.genblk1.i1.P` names nothing, even though
// the elaborator spells that block genblk1 and reaches what it holds under
// exactly that prefix.
//
// This is what tells a name the source wrote from one §27.6 assigned. The two
// are the same field by the time a generate block is elaborated, so without
// ModuleItem::name_is_generated a path resolved through both alike.
TEST(DefparamElaboration, GeneratedNameOfAnUnnamedGenerateBlockIsNotAPathStep) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module inner #(parameter int P = 5)();\n"
      "endmodule\n"
      "module outer;\n"
      "  if (1) begin\n"
      "    inner i1();\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  outer u();\n"
      "  defparam u.genblk1.i1.P = 99;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  auto* outer = ChildInstantiatedAs(design->top_modules[0], "u");
  ASSERT_NE(outer, nullptr);
  auto* inner = ChildInstantiatedAs(outer, "genblk1_i1");
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(inner->params[0].resolved_value, 5);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "defparam target not found",
                              10, "23.10.1"));
}

// m's parameter `name`, m declaring `items` among its own, instantiated once
// in top as u with `defparams` as top's defparam statements.
int64_t ParamOfMUnder(std::string_view items, std::string_view defparams,
                      std::string_view name, ElabFixture& f) {
  std::string src = "module m;\n";
  src += items;
  src +=
      "endmodule\n"
      "module top;\n"
      "  m u();\n";
  src += defparams;
  src += "endmodule\n";
  auto* design = ElaborateSrc(src, f, "top");
  return design == nullptr ? -1 : ParamValue(design, name);
}

// The same for an m declaring `parameter logic [TOP:0] P` after `parameter
// int TOP = 15`, Q set from P and B from $bits(P).
int64_t RangeDependentParamUnder(std::string_view defparams,
                                 std::string_view name, ElabFixture& f) {
  return ParamOfMUnder(
      "  parameter int TOP = 15;\n"
      "  parameter logic [TOP:0] P = 0;\n"
      "  localparam int Q = P;\n"
      "  localparam int B = $bits(P);\n",
      defparams, name, f);
}

// §6.20.2 (printed page 126): a parameter with a range specification has the
// range of its declaration, folded with the parameters in scope, and an
// override value is converted to it; §23.10.1 (printed 764-765) has a
// defparam's value take effect over the declaration's. `defparam u.TOP = 7`
// makes `logic [TOP:0] P` eight bits, so `defparam u.P = 16'hABCD` gives P
// 0xCD, which Q reads, and $bits(P) is 8. The defparam refolded the values of
// the parameters depending on TOP and left their ranges as first sized, so P
// stayed sixteen bits, Q read 0xABCD and B 16.
TEST(DefparamElaboration, ResizesAParameterWhoseRangeNamesTheOverriddenOne) {
  ElabFixture fq;
  EXPECT_EQ(RangeDependentParamUnder(
                "  defparam u.TOP = 7;\n  defparam u.P = 16'hABCD;\n", "Q", fq),
            0xCD);
  EXPECT_FALSE(fq.has_errors);
  ElabFixture fb;
  EXPECT_EQ(RangeDependentParamUnder(
                "  defparam u.TOP = 7;\n  defparam u.P = 16'hABCD;\n", "B", fb),
            8);
}

// The range alone made over: P keeps its declaration's own 0 and is eight
// bits wide.
TEST(DefparamElaboration, ResizesAParameterLeftAtItsDefault) {
  ElabFixture fq;
  EXPECT_EQ(RangeDependentParamUnder("  defparam u.TOP = 7;\n", "Q", fq), 0);
  ElabFixture fb;
  EXPECT_EQ(RangeDependentParamUnder("  defparam u.TOP = 7;\n", "B", fb), 8);
  EXPECT_FALSE(fb.has_errors);
}

// §23.10.1 (printed page 765) has a parameter take the value of the last
// defparam for it, and §6.20.2's conversion is to the range the parameter
// finally has: P given 0xABCD at sixteen bits, and TOP made 7 after that, is
// converted to the eight bits it now holds.
TEST(DefparamElaboration, ConvertsAnEarlierValueToTheRangeALaterDefparamSets) {
  ElabFixture f;
  EXPECT_EQ(RangeDependentParamUnder(
                "  defparam u.P = 16'hABCD;\n  defparam u.TOP = 7;\n", "Q", f),
            0xCD);
  EXPECT_FALSE(f.has_errors);
}

// The same with P declared through a typedef, `typedef logic [TOP:0] vec_t;
// parameter vec_t P = 0`.
int64_t TypedefRangedParamUnder(std::string_view defparams,
                                std::string_view name, ElabFixture& f) {
  return ParamOfMUnder(
      "  parameter int TOP = 15;\n"
      "  typedef logic [TOP:0] vec_t;\n"
      "  parameter vec_t P = 0;\n"
      "  localparam int Q = P;\n"
      "  localparam int B = $bits(P);\n",
      defparams, name, f);
}

// §6.18 (printed page 118) makes a typedef name stand for the type it was
// declared with, so `parameter vec_t P` under `typedef logic [TOP:0] vec_t`
// has the range §6.20.2 (printed 126) gives `logic [TOP:0]`, folded with
// TOP's final value: eight bits under `defparam u.TOP = 7`, so $bits(P) is 8
// and `defparam u.P = 16'hABCD` gives P 0xCD. A parameter declared through a
// typedef name was left as first sized, the typedef table not being in force
// where the defparam was applied, so B read 16 and Q 0xABCD.
TEST(DefparamElaboration, ResizesAParameterDeclaredThroughATypedef) {
  ElabFixture fb;
  EXPECT_EQ(TypedefRangedParamUnder("  defparam u.TOP = 7;\n", "B", fb), 8);
  EXPECT_FALSE(fb.has_errors);
  ElabFixture fq;
  EXPECT_EQ(TypedefRangedParamUnder(
                "  defparam u.TOP = 7;\n  defparam u.P = 16'hABCD;\n", "Q", fq),
            0xCD);
  EXPECT_FALSE(fq.has_errors);
}

// m's parameter `name`, m declaring `parameter logic [W-1:0] P = 0` after
// `parameter int W = 32`, H set from P[95:64], M from P[47:32] and B from
// $bits(P).
int64_t WideningParamUnder(std::string_view defparams, std::string_view name,
                           ElabFixture& f) {
  return ParamOfMUnder(
      "  parameter int W = 32;\n"
      "  parameter logic [W-1:0] P = 0;\n"
      "  localparam int H = P[95:64];\n"
      "  localparam int M = P[47:32];\n"
      "  localparam int B = $bits(P);\n",
      defparams, name, f);
}

// Top's defparams widening P before its value is set, and after it.
constexpr std::string_view kWidenThenSet =
    "  defparam u.W = 96;\n"
    "  defparam u.P = 96'h1_0000_0003_0000_0005;\n";
constexpr std::string_view kSetThenWiden =
    "  defparam u.P = 96'h1_0000_0003_0000_0005;\n"
    "  defparam u.W = 96;\n";

// §6.20.2 (printed page 126) converts an override value to the range of the
// parameter's declaration, and §23.10.1 (printed 764-765) has a defparam's
// value take effect over the declaration's, so `defparam u.W = 96` gives
// `logic [W-1:0] P` 96 bits and `defparam u.P = 96'h1_0000_0003_0000_0005`
// every digit of that literal: H reads its word above bit 64, 1, and $bits(P)
// 96. Sized again by W's defparam, P was converted from the value it held
// and its words above bit 63 were not recorded again, so H read 0.
TEST(DefparamElaboration, RecordsAWidenedDefparamValuesWordsAboveSixtyFour) {
  ElabFixture fh;
  EXPECT_EQ(WideningParamUnder(kWidenThenSet, "H", fh), 1);
  EXPECT_FALSE(fh.has_errors);
  ElabFixture fb;
  EXPECT_EQ(WideningParamUnder(kWidenThenSet, "B", fb), 96);
}

// The defparams in the other order: P's value was converted to the 32 bits
// it then had, and W's defparam widening it to 96 converts the right-hand
// side over again to the new range rather than the 5 the first conversion
// left, so M reads the 3 at bits 47 down to 32 and H the 1 above bit 64.
TEST(DefparamElaboration, RefoldsADefparamValueALaterDefparamWidens) {
  ElabFixture fh;
  EXPECT_EQ(WideningParamUnder(kSetThenWiden, "H", fh), 1);
  EXPECT_FALSE(fh.has_errors);
  ElabFixture fm;
  EXPECT_EQ(WideningParamUnder(kSetThenWiden, "M", fm), 3);
}

// §11.6.1 (printed page 299) with §23.10.1 (printed 764-765): a defparam's
// right-hand side is assigned to the parameter, so its context-determined
// operands are sized by the parameter's declared width before the operator
// is applied, as a declaration's own value is (§11.8.2, printed 302).
// Folded at the operands' own widths, `defparam u.P = 8'hAB << 8` over
// `parameter [15:0] P` shifted at 8 bits and gave P 0, and `defparam u.X = 3
// ** 50` over `parameter logic [95:0] X` raised 3 at 32 bits and left X's
// word above bit 64, 0x9805 of 3^50 = 0x9805_53F0DB2F_D09DE3C9, reading 0.
TEST(DefparamElaboration, SizesADefparamValueByTheParametersDeclaredWidth) {
  constexpr std::string_view kItems =
      "  parameter [15:0] P = 0;\n"
      "  parameter logic [95:0] X = 0;\n"
      "  localparam int XH = X[95:64];\n";
  constexpr std::string_view kDefparams =
      "  defparam u.P = 8'hAB << 8;\n"
      "  defparam u.X = 3 ** 50;\n";
  ElabFixture fp;
  EXPECT_EQ(ParamOfMUnder(kItems, kDefparams, "P", fp), 0xAB00);
  EXPECT_FALSE(fp.has_errors);
  ElabFixture fx;
  EXPECT_EQ(ParamOfMUnder(kItems, kDefparams, "XH", fx), 0x9805);
}

// A defparam on any parameter of m has the values of m's other parameters
// folded again (RecomputeDependentParams), and that fold sizes a default by
// the declared width as the first did: `parameter [15:0] W = 8'hFF + 8'h01`
// keeps 0x100 under `defparam u.A = 2`, where a fold at the operands' 8 bits
// dropped the carry and left W 0.
TEST(DefparamElaboration, RefoldsAnotherParametersDefaultInItsDeclaredWidth) {
  ElabFixture f;
  EXPECT_EQ(ParamOfMUnder("  parameter A = 1;\n"
                          "  parameter [15:0] W = 8'hFF + 8'h01;\n",
                          "  defparam u.A = 2;\n", "W", f),
            0x100);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
