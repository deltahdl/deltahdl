#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(CaseViolationDeferralSim, DeferredUniqueCaseOverlapReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    unique case(sel)\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationDeferralSim, DeferredPriorityCaseNoMatchReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    x = 8'd0;\n"
      "    priority case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationDeferralSim, DeferredUniqueCaseNoMatchReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd99;\n"
      "    x = 8'd0;\n"
      "    unique case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationDeferralSim, Unique0CaseNoMatchNoDeferredViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    x = 8'd0;\n"
      "    unique0 case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseViolationDeferralSim, Unique0CaseOverlapDeferredViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique0 case(8'd1)\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationDeferralSim, DeferredUniqueCasezOverlapReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'b00000001;\n"
      "    unique casez(sel)\n"
      "      8'b0000???1: x = 8'd10;\n"
      "      8'b000000?1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationDeferralSim, AlwaysCombRetriggerFlushesCaseViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  always_comb begin\n"
      "    unique case (1'b1)\n"
      "      a: z = 8'd1;\n"
      "      b: z = 8'd2;\n"
      "      default: z = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    b <= 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseViolationDeferralSim, AlwaysCombRetriggerFlushesNoMatchViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  always_comb begin\n"
      "    unique case (1'b1)\n"
      "      a: z = 8'd1;\n"
      "      b: z = 8'd2;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    b = 1'b0;\n"
      "    a <= 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  const uint32_t kBeforeRun = f.diag.WarningCount();
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), kBeforeRun);
}

TEST(CaseViolationDeferralSim, AlwaysLatchRetriggerFlushesCaseViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  always_latch begin\n"
      "    unique case (1'b1)\n"
      "      a: z = 8'd1;\n"
      "      b: z = 8'd2;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    b <= 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseViolationDeferralSim, DeferredPriorityCasexNoMatchReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd99;\n"
      "    x = 8'd0;\n"
      "    priority casex(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationDeferralSim, EventControlFlushesCaseViolation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique case (8'd1)\n"
      "      8'd1: x = 8'd1;\n"
      "      8'd1: x = 8'd2;\n"
      "    endcase\n"
      "    @e;\n"
      "    x = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    -> e;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseViolationDeferralSim, WaitStatementFlushesCaseViolation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic ready;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    ready = 1'b0;\n"
      "    unique case (8'd1)\n"
      "      8'd1: x = 8'd1;\n"
      "      8'd1: x = 8'd2;\n"
      "    endcase\n"
      "    wait (ready);\n"
      "    x = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    ready = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseViolationDeferralSim, MaturedCaseViolationSurvivesLaterResume) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique case (8'd1)\n"
      "      8'd1: x = 8'd1;\n"
      "      8'd1: x = 8'd2;\n"
      "    endcase\n"
      "    @e;\n"
      "    x = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> e;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationDeferralSim, UniqueCaseOverlapNames12_5_3_1) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] s, y;\n"
      "  initial begin\n"
      "    s = 8'd2;\n"
      "    unique case(s)\n"
      "      8'd2: y = 8'd30;\n"
      "      8'd2: y = 8'd40;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "unique case: multiple items matched", 5,
                              "12.5.3.1"));
}

}  // namespace
