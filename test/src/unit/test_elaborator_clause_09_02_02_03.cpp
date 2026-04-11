#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(AlwaysLatchElaboration, TimingControlInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch #5 if (en) q = d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysLatchElaboration, ForkJoinInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysLatchElaboration, IncompleteIfNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysLatchElaboration, CompleteIfElseWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch\n"
      "    if (en) q = a;\n"
      "    else q = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysLatchElaboration, CaseWithoutDefaultNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic q;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b00: q = 0;\n"
      "      2'b01: q = 1;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysLatchElaboration, CaseWithDefaultWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic q;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b00: q = 0;\n"
      "      2'b01: q = 1;\n"
      "      default: q = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysLatchElaboration, AlwaysLatchElaboratesToCorrectKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysLatch) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(AlwaysLatchElaboration, MultiDriverTwoAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch if (en) q = a;\n"
      "  always_latch if (en) q = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysLatchElaboration, AlwaysLatchInfersSensitivityFromBody) {
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

TEST(AlwaysLatchElaboration, EventControlInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, d, q, clk;\n"
      "  always_latch @(posedge clk) if (en) q = d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysLatchElaboration, UnconditionalAssignWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic d, q;\n"
      "  always_latch q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysLatchElaboration, IfElseIfElseChainWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, d1, d2, d3, q;\n"
      "  always_latch\n"
      "    if (a) q = d1;\n"
      "    else if (b) q = d2;\n"
      "    else q = d3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysLatchElaboration, TwoAlwaysLatchDifferentSignalsNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q1, q2;\n"
      "  always_latch if (en) q1 = a;\n"
      "  always_latch if (en) q2 = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
