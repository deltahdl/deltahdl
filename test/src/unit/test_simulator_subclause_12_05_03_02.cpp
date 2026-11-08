#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(CaseViolationMultiProcessSim, TwoProcessesBothOverlapReportedTwice) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x, y;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    unique case(sel)\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    sel = 8'd2;\n"
      "    unique case(sel)\n"
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

  EXPECT_GE(f.diag.WarningCount(), 2u);
}

TEST(CaseViolationMultiProcessSim, OneProcessViolatesOtherDoesNot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    unique case(8'd1)\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    unique case(8'd1)\n"
      "      8'd0: y = 8'd30;\n"
      "      8'd1: y = 8'd40;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationMultiProcessSim, TwoProcessesNoMatchBothReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    priority case(8'd5)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    y = 8'd0;\n"
      "    priority case(8'd5)\n"
      "      8'd0: y = 8'd30;\n"
      "      8'd1: y = 8'd40;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_GE(f.diag.WarningCount(), 2u);
}

TEST(CaseViolationMultiProcessSim, Unique0OverlapReportsNoMatchSilent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    unique0 case(8'd1)\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    y = 8'd0;\n"
      "    unique0 case(8'd99)\n"
      "      8'd0: y = 8'd30;\n"
      "      8'd1: y = 8'd40;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationMultiProcessSim, TaskUniqueCaseOverlapReportsViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  task chk(input bit [7:0] s);\n"
      "    unique case(s)\n"
      "      8'd1: r = 8'd10;\n"
      "      8'd1: r = 8'd20;\n"
      "    endcase\n"
      "  endtask\n"
      "  initial chk(8'd1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationMultiProcessSim, TwoProcessesCallSharedTaskCaseReportTwice) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  task chk(input bit [7:0] s);\n"
      "    unique case(s)\n"
      "      8'd1: r = 8'd10;\n"
      "      8'd1: r = 8'd20;\n"
      "    endcase\n"
      "  endtask\n"
      "  initial chk(8'd1);\n"
      "  initial chk(8'd1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 2u);
}

TEST(CaseViolationMultiProcessSim, SharedTaskCaseOneCallerViolatesOtherPasses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  task chk(input bit [7:0] s);\n"
      "    unique case(s)\n"
      "      8'd1: r = 8'd10;\n"
      "      8'd1: r = 8'd20;\n"
      "      8'd2: r = 8'd30;\n"
      "    endcase\n"
      "  endtask\n"
      "  initial chk(8'd1);\n"
      "  initial chk(8'd2);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationMultiProcessSim, RetriggerFlushInOneProcessSparesOther) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z, w;\n"
      "  always_comb begin\n"
      "    unique case (1'b1)\n"
      "      a: z = 8'd1;\n"
      "      b: z = 8'd2;\n"
      "      default: z = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    unique case (8'd1)\n"
      "      8'd1: w = 8'd10;\n"
      "      8'd1: w = 8'd20;\n"
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
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

}  // namespace
