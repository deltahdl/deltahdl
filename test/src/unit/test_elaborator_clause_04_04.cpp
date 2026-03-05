#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- §4.4: Sensitivity and region-related elaboration ---

TEST(ElabCh44, AlwaysCombInfersSensitivityFromBody) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_FALSE(mod->processes[0].sensitivity.empty());
}

TEST(ElabCh44, AlwaysLatchInfersSensitivityFromBody) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch if (en) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_FALSE(mod->processes[0].sensitivity.empty());
}

TEST(ElabCh44, AlwaysFFPreservesExplicitSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  ASSERT_FALSE(mod->processes[0].sensitivity.empty());
  EXPECT_EQ(mod->processes[0].sensitivity[0].edge, Edge::kPosedge);
}

TEST(ElabCh44, PlainAlwaysPreservesExplicitSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  always @(posedge clk) x = ~x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  ASSERT_FALSE(mod->processes[0].sensitivity.empty());
  EXPECT_EQ(mod->processes[0].sensitivity[0].edge, Edge::kPosedge);
}

TEST(ElabCh44, InitialHasNoSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_TRUE(mod->processes[0].sensitivity.empty());
}

TEST(ElabCh44, FinalHasNoSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_TRUE(mod->processes[0].sensitivity.empty());
}

TEST(ElabCh44, AlwaysCombMultipleReadsInferMultipleSensitivities) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c;\n"
      "  always_comb c = a + b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_GE(mod->processes[0].sensitivity.size(), 2u);
}

TEST(ElabCh44, AlwaysFFNegedgeSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(negedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  ASSERT_FALSE(mod->processes[0].sensitivity.empty());
  EXPECT_EQ(mod->processes[0].sensitivity[0].edge, Edge::kNegedge);
}

TEST(ElabCh44, InferredSensitivityEdgeIsNone) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  ASSERT_FALSE(mod->processes[0].sensitivity.empty());
  EXPECT_EQ(mod->processes[0].sensitivity[0].edge, Edge::kNone);
}

TEST(ElabCh44, AlwaysFFWithResetSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, rst, d, q;\n"
      "  always_ff @(posedge clk or negedge rst)\n"
      "    if (!rst) q <= 0;\n"
      "    else q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  ASSERT_GE(mod->processes[0].sensitivity.size(), 2u);
  EXPECT_EQ(mod->processes[0].sensitivity[0].edge, Edge::kPosedge);
  EXPECT_EQ(mod->processes[0].sensitivity[1].edge, Edge::kNegedge);
}

TEST(ElabCh44, AlwaysCombDoesNotIncludeWrittenVarsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  // Sensitivity should include 'a' but not 'b'.
  ASSERT_FALSE(mod->processes[0].sensitivity.empty());
  EXPECT_EQ(mod->processes[0].sensitivity.size(), 1u);
}

TEST(ElabCh44, MultipleAlwaysCombProcessesIndependentSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  always_comb c = a;\n"
      "  always_comb d = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 2u);
  EXPECT_FALSE(mod->processes[0].sensitivity.empty());
  EXPECT_FALSE(mod->processes[1].sensitivity.empty());
}

TEST(ElabCh44, PlainAlwaysWithStarSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always @(*) b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_FALSE(mod->processes[0].sensitivity.empty());
}

}  // namespace
