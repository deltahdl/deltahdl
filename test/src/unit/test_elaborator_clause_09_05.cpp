#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ProcessExecutionThreadElaboration, InitialCreatesProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->processes.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kInitial);
}

TEST(ProcessExecutionThreadElaboration, FinalCreatesProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  final x = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->processes.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kFinal);
}

TEST(ProcessExecutionThreadElaboration, AlwaysCreatesProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  always @(posedge clk) x = ~x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->processes.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kAlways);
}

TEST(ProcessExecutionThreadElaboration, AlwaysCombCreatesProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->processes.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kAlwaysComb);
}

TEST(ProcessExecutionThreadElaboration, AlwaysLatchCreatesProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->processes.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kAlwaysLatch);
}

TEST(ProcessExecutionThreadElaboration, AlwaysFFCreatesProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->processes.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->processes[0].kind,
            RtlirProcessKind::kAlwaysFF);
}

TEST(ProcessExecutionThreadElaboration, MultipleProceduresCreateMultipleProcesses) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  initial a = 0;\n"
      "  always @(posedge clk) b = ~b;\n"
      "  always_comb c = a;\n"
      "  final a = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->processes.size(), 4u);
}

TEST(ProcessExecutionThreadElaboration, ContAssignSeparateFromProcesses) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  assign b = a;\n"
      "  initial a = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->processes.size(), 1u);
  EXPECT_GE(design->top_modules[0]->assigns.size(), 1u);
}

TEST(ProcessExecutionThreadElaboration, MultipleProcessKindsInOneModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  initial a = 0;\n"
      "  always_comb b = a;\n"
      "  always_ff @(posedge clk) c <= b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 3u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
  EXPECT_EQ(mod->processes[1].kind, RtlirProcessKind::kAlwaysComb);
  EXPECT_EQ(mod->processes[2].kind, RtlirProcessKind::kAlwaysFF);
}

TEST(ProcessExecutionThreadElaboration, InitialAndFinalCoexist) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = 1;\n"
      "  final $display(\"done\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 2u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
  EXPECT_EQ(mod->processes[1].kind, RtlirProcessKind::kFinal);
}

TEST(ProcessExecutionThreadElaboration, AllSixProcessKindsInOneModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c, d, e;\n"
      "  initial a = 0;\n"
      "  final $display(\"end\");\n"
      "  always @(posedge clk) b = ~b;\n"
      "  always_comb c = a;\n"
      "  always_ff @(posedge clk) d <= a;\n"
      "  always_latch if (clk) e <= a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 6u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
  EXPECT_EQ(mod->processes[1].kind, RtlirProcessKind::kFinal);
  EXPECT_EQ(mod->processes[2].kind, RtlirProcessKind::kAlways);
  EXPECT_EQ(mod->processes[3].kind, RtlirProcessKind::kAlwaysComb);
  EXPECT_EQ(mod->processes[4].kind, RtlirProcessKind::kAlwaysFF);
  EXPECT_EQ(mod->processes[5].kind, RtlirProcessKind::kAlwaysLatch);
}

TEST(ProcessExecutionThreadElaboration, ModuleWithOnlyContinuousAssignsHasNoProcesses) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c;\n"
      "  assign b = a;\n"
      "  assign c = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->processes.size(), 0u);
  EXPECT_GE(mod->assigns.size(), 2u);
}

TEST(ProcessExecutionThreadElaboration, EachInitialCreatesOwnProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c;\n"
      "  initial a = 0;\n"
      "  initial b = 1;\n"
      "  initial c = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 3u);
  for (auto& p : mod->processes) {
    EXPECT_EQ(p.kind, RtlirProcessKind::kInitial);
  }
}

TEST(ProcessExecutionThreadElaboration, EachAlwaysCombCreatesOwnProcess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, y1, y2;\n"
      "  always_comb y1 = a;\n"
      "  always_comb y2 = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 2u);
  for (auto& p : mod->processes) {
    EXPECT_EQ(p.kind, RtlirProcessKind::kAlwaysComb);
  }
}

TEST(ProcessExecutionThreadElaboration, EachContAssignCreatesOwnThread) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  assign b = a;\n"
      "  assign c = a;\n"
      "  assign d = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->processes.size(), 0u);
  EXPECT_GE(mod->assigns.size(), 3u);
}

}  // namespace
