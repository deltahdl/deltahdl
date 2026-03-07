#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §9.5: Each initial procedure creates a process thread.
TEST(ElabClause09_05, InitialCreatesProcess) {
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

// §9.5: Each final procedure creates a process thread.
TEST(ElabClause09_05, FinalCreatesProcess) {
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

// §9.5: Each always procedure creates a process thread.
TEST(ElabClause09_05, AlwaysCreatesProcess) {
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

// §9.5: Each always_comb creates a process thread.
TEST(ElabClause09_05, AlwaysCombCreatesProcess) {
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

// §9.5: Each always_latch creates a process thread.
TEST(ElabClause09_05, AlwaysLatchCreatesProcess) {
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

// §9.5: Each always_ff creates a process thread.
TEST(ElabClause09_05, AlwaysFFCreatesProcess) {
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

// §9.5: Multiple procedures each create their own process thread.
TEST(ElabClause09_05, MultipleProceduresCreateMultipleProcesses) {
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

// §9.5: Continuous assignments are separate from process threads.
TEST(ElabClause09_05, ContAssignSeparateFromProcesses) {
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

}  // namespace
