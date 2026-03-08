#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabCh49, ContinuousAssignElaboratesToRtlirAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  assign b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_NE(mod->assigns[0].rhs, nullptr);
}

TEST(ElabCh49, MultipleContinuousAssigns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c;\n"
      "  assign b = a;\n"
      "  assign c = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->assigns.size(), 2u);
}

TEST(ElabCh49, ContinuousAssignWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  assign b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].width, 8u);
}

TEST(ElabCh49, ContinuousAssignSeparateFromProcesses) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c;\n"
      "  assign b = a;\n"
      "  initial c = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->assigns.size(), 1u);
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
}

TEST(ElabCh49, BlockingAssignInInitialIsProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    x = x + 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
  EXPECT_NE(mod->processes[0].body, nullptr);
}

TEST(ElabCh49, NonblockingAssignInAlwaysFFIsProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [7:0] d, q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlwaysFF);
}

TEST(ElabCh49, MixedAssignmentTypesElaborateCorrectly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  assign b = a;\n"
      "  initial a = 0;\n"
      "  always_ff @(posedge clk) c <= b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->assigns.size(), 1u);
  ASSERT_EQ(mod->processes.size(), 2u);
}

TEST(ElabCh49, ContinuousAssignChainElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  assign b = a + 8'd1;\n"
      "  assign c = b + 8'd1;\n"
      "  assign d = c + 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->assigns.size(), 3u);
}

TEST(ElabCh49, SingleBitContinuousAssignWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  assign b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].width, 1u);
}

TEST(ElabCh49, WideContinuousAssign32Bit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  assign b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].width, 32u);
}

TEST(ElabCh49, AlwaysCombAssignIsProcessNotContinuous) {
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
  EXPECT_EQ(mod->assigns.size(), 0u);
  EXPECT_EQ(mod->processes.size(), 1u);
}

TEST(ElabCh49, NonblockingAssignInAlwaysLatch) {
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
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlwaysLatch);
}

TEST(ElabCh49, MultipleAssignStatementsInInitialBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    y = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
  EXPECT_EQ(mod->assigns.size(), 0u);
}

}
