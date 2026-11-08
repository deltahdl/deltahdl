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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "defparam right-hand side must be a constant expression "
                    "built from numbers and parameters",
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
  EXPECT_EQ(u->params[0].resolved_value, 5);
  EXPECT_TRUE(u->params[0].is_resolved);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "defparam inside a generate block or an array of instances "
                    "reaches a parameter outside that hierarchy",
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "defparam inside a generate block or an array of instances "
                    "reaches a parameter outside that hierarchy",
                    8, "23.10.1"));
}

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

int64_t RangeDependentParamUnder(std::string_view defparams,
                                 std::string_view name, ElabFixture& f) {
  return ParamOfMUnder(
      "  parameter int TOP = 15;\n"
      "  parameter logic [TOP:0] P = 0;\n"
      "  localparam int Q = P;\n"
      "  localparam int B = $bits(P);\n",
      defparams, name, f);
}

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

TEST(DefparamElaboration, ResizesAParameterLeftAtItsDefault) {
  ElabFixture fq;
  EXPECT_EQ(RangeDependentParamUnder("  defparam u.TOP = 7;\n", "Q", fq), 0);
  ElabFixture fb;
  EXPECT_EQ(RangeDependentParamUnder("  defparam u.TOP = 7;\n", "B", fb), 8);
  EXPECT_FALSE(fb.has_errors);
}

TEST(DefparamElaboration, ConvertsAnEarlierValueToTheRangeALaterDefparamSets) {
  ElabFixture f;
  EXPECT_EQ(RangeDependentParamUnder(
                "  defparam u.P = 16'hABCD;\n  defparam u.TOP = 7;\n", "Q", f),
            0xCD);
  EXPECT_FALSE(f.has_errors);
}

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

constexpr std::string_view kWidenThenSet =
    "  defparam u.W = 96;\n"
    "  defparam u.P = 96'h1_0000_0003_0000_0005;\n";
constexpr std::string_view kSetThenWiden =
    "  defparam u.P = 96'h1_0000_0003_0000_0005;\n"
    "  defparam u.W = 96;\n";

TEST(DefparamElaboration, RecordsAWidenedDefparamValuesWordsAboveSixtyFour) {
  ElabFixture fh;
  EXPECT_EQ(WideningParamUnder(kWidenThenSet, "H", fh), 1);
  EXPECT_FALSE(fh.has_errors);
  ElabFixture fb;
  EXPECT_EQ(WideningParamUnder(kWidenThenSet, "B", fb), 96);
}

TEST(DefparamElaboration, RefoldsADefparamValueALaterDefparamWidens) {
  ElabFixture fh;
  EXPECT_EQ(WideningParamUnder(kSetThenWiden, "H", fh), 1);
  EXPECT_FALSE(fh.has_errors);
  ElabFixture fm;
  EXPECT_EQ(WideningParamUnder(kSetThenWiden, "M", fm), 3);
}

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

TEST(DefparamElaboration, RefoldsAnotherParametersDefaultInItsDeclaredWidth) {
  ElabFixture f;
  EXPECT_EQ(ParamOfMUnder("  parameter A = 1;\n"
                          "  parameter [15:0] W = 8'hFF + 8'h01;\n",
                          "  defparam u.A = 2;\n", "W", f),
            0x100);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
