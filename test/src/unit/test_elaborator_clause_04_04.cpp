#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StratifiedSchedulerElaboration, AlwaysFFPreservesExplicitSensitivity) {
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

TEST(StratifiedSchedulerElaboration, PlainAlwaysPreservesExplicitSensitivity) {
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

TEST(StratifiedSchedulerElaboration, InitialHasNoSensitivity) {
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

TEST(StratifiedSchedulerElaboration, FinalHasNoSensitivity) {
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

TEST(StratifiedSchedulerElaboration, AlwaysFFNegedgeSensitivity) {
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

TEST(StratifiedSchedulerElaboration, AlwaysFFWithResetSensitivity) {
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

}  // namespace
