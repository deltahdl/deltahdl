#include <gtest/gtest.h>

#include <set>
#include <string>

#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(GenerateElaboration, GenerateForCreatesVars) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 3) ();\n"
      "  generate\n"
      "    for (genvar i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[0].name, "genblk1_0_x");
  EXPECT_EQ(mod->variables[1].name, "genblk1_1_x");
  EXPECT_EQ(mod->variables[2].name, "genblk1_2_x");
}

TEST(GenerateElaboration, GenerateForZeroIterations) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 0) ();\n"
      "  generate\n"
      "    for (genvar i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 0u);
}

TEST(GenerateElaboration, GenerateForWithAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 2) ();\n"
      "  generate\n"
      "    for (genvar i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] w;\n"
      "      assign w = 100;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->assigns.size(), 2u);
  EXPECT_EQ(mod->variables[0].name, "genblk1_0_w");
  EXPECT_EQ(mod->variables[1].name, "genblk1_1_w");
}

TEST(GenerateElaboration, GenerateForCreatesInstances) {
  ElabFixture f;
  auto* design = Elaborate(
      "module sub(input logic a); endmodule\n"
      "module top #(parameter N = 2) ();\n"
      "  generate\n"
      "    for (genvar i = 0; i < N; i = i + 1) begin : blk\n"
      "      sub u(.a(1'b0));\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->children.size(), 2u);
}

TEST(GenerateElaboration, GenerateForStepByTwo) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter N = 6) ();\n"
      "  generate\n"
      "    for (genvar i = 0; i < N; i = i + 2) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 3u);
}

TEST(GenerateElaboration, NestedGenerateForIf) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter N = 2) ();\n"
      "  generate\n"
      "    for (genvar i = 0; i < N; i = i + 1) begin\n"
      "      if (1) begin\n"
      "        logic [7:0] inner;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->variables.size(), 2u);
}

TEST(GenerateElaboration, GenerateForNonTerminatingLoopErrors) {
  ElabFixture f;
  f.configure = [](Elaborator& elab) { elab.SetMaxGenerateIterations(256); };
  ElabOk(
      "module top();\n"
      "  generate\n"
      "    for (genvar i = 0; i >= 0; i = i + 1) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "loop generate scheme did not terminate within 256 iterations", 3,
      "27.4"));
}

TEST(GenerateElaboration, LoopGenerateAboveTheOldBoundElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 65600) ();\n"
      "  generate\n"
      "    for (genvar i = 0; i < N; i = i + 1) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->variables.size(), 65600u);
}

TEST(GenerateElaboration, LoopGenerateBoundDecidesWhetherASchemeIsReported) {
  const std::string kSrc =
      "module t #(parameter N = 300) ();\n"
      "  generate\n"
      "    for (genvar i = 0; i < N; i = i + 1) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n";

  ElabFixture tight;
  tight.configure = [](Elaborator& elab) {
    elab.SetMaxGenerateIterations(256);
  };
  ElaborateSrc(kSrc, tight);
  EXPECT_TRUE(ReportedError(
      tight.diag.Diagnostics(),
      "loop generate scheme did not terminate within 256 iterations", 3,
      "27.4"));

  ElabFixture roomy;
  roomy.configure = [](Elaborator& elab) {
    elab.SetMaxGenerateIterations(1024);
  };
  auto* design = ElaborateSrc(kSrc, roomy);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(roomy.has_errors);
  EXPECT_EQ(design->top_modules[0]->variables.size(), 300u);
}

TEST(GenerateElaboration, GenerateForRepeatedGenvarValueErrors) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  generate\n"
      "    for (genvar i = 5; i < 10; i = 5) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for genvar value is repeated during "
                            "evaluation",
                            3, "27.4"));
}

TEST(GenerateElaboration, GenerateForInitStepDifferentVariablesErrors) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  genvar i, j;\n"
      "  generate\n"
      "    for (i = 0; i < 3; j = j + 1) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate-for init and step assign different genvars", 4, "27.4"));
}

TEST(GenerateElaboration, GenerateForInitReferencesOwnGenvarErrors) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  generate\n"
      "    for (genvar i = i + 1; i < 3; i = i + 1) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for init reads the loop's own genvar on "
                            "its right-hand side",
                            3, "27.4"));
}

TEST(GenerateElaboration, GenerateForNamedBlockConflictsWithVariableErrors) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  logic a;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 1; i < 0; i = i + 1) begin : a\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block array 'a' conflicts with an "
                            "existing declaration in the same scope",
                            5, "27.4"));
}

TEST(GenerateElaboration, GenerateForDuplicateBlockArrayNameErrors) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 1; i < 5; i = i + 1) begin : a\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "    for (i = 10; i < 15; i = i + 1) begin : a\n"
      "      logic [7:0] y;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block array 'a' conflicts with an "
                            "existing declaration in the same scope",
                            7, "27.4"));
}

TEST(GenerateElaboration, NestedBlockArrayNameRepeatsPerOuterInstanceOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  genvar i, j;\n"
      "  generate\n"
      "    for (i = 0; i < 2; i = i + 1) begin : g\n"
      "      for (j = 0; j < 2; j = j + 1) begin : h\n"
      "        logic [7:0] x;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->top_modules[0]->variables.size(), 4u);
}

TEST(GenerateElaboration, SiblingBlockArrayNamesInsideOneBlockConflictErrors) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  genvar i, j, k;\n"
      "  generate\n"
      "    for (i = 0; i < 2; i = i + 1) begin : g\n"
      "      for (j = 0; j < 2; j = j + 1) begin : h\n"
      "        logic [7:0] x;\n"
      "      end\n"
      "      for (k = 0; k < 2; k = k + 1) begin : h\n"
      "        logic [7:0] y;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block array 'h' conflicts with an "
                            "existing declaration in the same scope",
                            8, "27.4"));
}

TEST(GenerateElaboration, GenerateForGenvarXZInitErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  generate\n"
      "    for (genvar i = 2'b1x; i < 3; i = i + 1) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for genvar must hold no x or z bit while "
                            "the loop is evaluated, and the initialization "
                            "assignment sets one",
                            3, "27.4"));
}

TEST(GenerateElaboration, GenerateForGenvarXZStepErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  generate\n"
      "    for (genvar i = 0; i < 3; i = 2'b0z) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for genvar must hold no x or z bit while "
                            "the loop is evaluated, and the iteration "
                            "assignment sets one",
                            3, "27.4"));
}

TEST(GenerateElaboration, GenerateForGenvarXZReportsNameWhichHalfOfTheHeader) {
  constexpr const char* kInitMsg =
      "generate-for genvar must hold no x or z bit while the loop is "
      "evaluated, and the initialization assignment sets one";
  constexpr const char* kIterationMsg =
      "generate-for genvar must hold no x or z bit while the loop is "
      "evaluated, and the iteration assignment sets one";

  ElabFixture init;
  ElaborateSrc(
      "module top();\n"
      "  generate\n"
      "    for (genvar i = 2'b1x; i < 3; i = i + 1) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      init);
  EXPECT_TRUE(ReportedError(init.diag.Diagnostics(), kInitMsg, 3, "27.4"));
  EXPECT_FALSE(
      ReportedError(init.diag.Diagnostics(), kIterationMsg, 3, "27.4"));

  ElabFixture step;
  ElaborateSrc(
      "module top();\n"
      "  generate\n"
      "    for (genvar i = 0; i < 3; i = 2'b0z) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      step);
  EXPECT_TRUE(ReportedError(step.diag.Diagnostics(), kIterationMsg, 3, "27.4"));
  EXPECT_FALSE(ReportedError(step.diag.Diagnostics(), kInitMsg, 3, "27.4"));
}

static std::set<std::string> VariableNames(const RtlirModule* mod) {
  std::set<std::string> names;
  for (const auto& var : mod->variables) names.insert(std::string(var.name));
  return names;
}

TEST(GenerateElaboration,
     SiblingNamedBlocksOverOneGenvarNameTheirDeclarationsApart) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 4; i < 6; i = i + 1) begin : blk_a\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "    for (i = 4; i < 6; i = i + 1) begin : blk_b\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 4u);
  EXPECT_EQ(VariableNames(mod),
            (std::set<std::string>{"blk_a_4_v", "blk_a_5_v", "blk_b_4_v",
                                   "blk_b_5_v"}));
}

TEST(GenerateElaboration,
     SiblingNamedBlocksOverOneGenvarStampDistinctContAssignPrefixes) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 4; i < 5; i = i + 1) begin : blk_a\n"
      "      logic [7:0] a;\n"
      "      assign a = 8'd11;\n"
      "    end\n"
      "    for (i = 4; i < 5; i = i + 1) begin : blk_b\n"
      "      logic [7:0] b;\n"
      "      assign b = 8'd22;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->assigns.size(), 2u);
  ASSERT_FALSE(mod->assigns[0].gen_block_prefixes.empty());
  ASSERT_FALSE(mod->assigns[1].gen_block_prefixes.empty());
  std::string first(mod->assigns[0].gen_block_prefixes.back());
  std::string second(mod->assigns[1].gen_block_prefixes.back());
  EXPECT_NE(first, second);
}

TEST(GenerateElaboration,
     SiblingUnnamedBlocksOverOneGenvarNameTheirDeclarationsApart) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 4; i < 6; i = i + 1) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "    for (i = 4; i < 6; i = i + 1) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 4u);
  EXPECT_EQ(VariableNames(mod),
            (std::set<std::string>{"genblk1_4_v", "genblk1_5_v", "genblk2_4_v",
                                   "genblk2_5_v"}));
}

static std::set<std::string> InstanceNames(const RtlirModule* mod) {
  std::set<std::string> names;
  for (const auto& child : mod->children)
    names.insert(std::string(child.inst_name));
  return names;
}

TEST(GenerateElaboration, LoopGenerateBlockNamesEachIterationsInstanceApart) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub; endmodule\n"
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 4; i < 6; i = i + 1) begin : blk\n"
      "      sub u();\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 2u);
  EXPECT_EQ(InstanceNames(mod), (std::set<std::string>{"blk_4_u", "blk_5_u"}));
}

TEST(GenerateElaboration,
     SiblingNamedBlocksOverOneGenvarNameTheirInstancesApart) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub; endmodule\n"
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 4; i < 6; i = i + 1) begin : blk_a\n"
      "      sub u();\n"
      "    end\n"
      "    for (i = 4; i < 6; i = i + 1) begin : blk_b\n"
      "      sub u();\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 4u);
  EXPECT_EQ(InstanceNames(mod),
            (std::set<std::string>{"blk_a_4_u", "blk_a_5_u", "blk_b_4_u",
                                   "blk_b_5_u"}));
}

}  // namespace
