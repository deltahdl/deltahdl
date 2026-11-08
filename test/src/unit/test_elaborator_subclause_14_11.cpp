#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CycleDelayElab, WithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
}

TEST(CycleDelayElab, WithDefaultClockingNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CycleDelayElab, WithReferenceFormDefaultClockingNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CycleDelayElab, ProgramScopeWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endprogram\n"
      "module top;\n"
      "  p pi();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
}

TEST(CycleDelayElab, ProgramScopeWithDefaultClockingNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endprogram\n"
      "module top;\n"
      "  p pi();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CycleDelayElab, InterfaceScopeWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endinterface\n"
      "module top;\n"
      "  intf ii();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
}

TEST(CycleDelayElab, InterfaceScopeWithDefaultClockingNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endinterface\n"
      "module top;\n"
      "  intf ii();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CycleDelayElab, CheckerScopeWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  checker chk;\n"
      "    initial begin\n"
      "      ##5;\n"
      "    end\n"
      "  endchecker\n"
      "  chk c1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 3, "14.11"));
}

TEST(CycleDelayElab, CheckerInitialCycleDelayRejectedWithDefaultClocking) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  checker chk; logic clk;\n"
      "    logic data; default clocking cb @(posedge clk);\n"
      "      input data;\n"
      "    endclocking\n"
      "    initial begin\n"
      "      ##5;\n"
      "    end\n"
      "  endchecker\n"
      "  chk c1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "an initial procedure in checker 'chk' may use only an event control", 6,
      "17.5"));
}

TEST(CycleDelayElab, NestedCycleDelayWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    if (1) begin\n"
      "      ##5;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
}

TEST(CycleDelayElab, IntraAssignBlockingCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    a = ##3 b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 6, "14.11"));
}

TEST(CycleDelayElab, IntraAssignNonblockingCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    a <= ##3 b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 6, "14.11"));
}

TEST(CycleDelayElab, NestedIntraAssignCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    if (1) begin\n"
      "      a <= ##2 b;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 7, "14.11"));
}

TEST(CycleDelayElab, IntraAssignBitSelectLhsCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a[3] = ##3 b[0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 7, "14.11"));
}

TEST(CycleDelayElab, IntraAssignPartSelectLhsCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a[3:0] <= ##2 b[3:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 7, "14.11"));
}

TEST(CycleDelayElab, IntraAssignConcatLhsCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] c;\n"
      "  initial begin\n"
      "    {a, b} = ##3 c;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 8, "14.11"));
}

TEST(CycleDelayElab, SynchronousDriveBitSelectWithCycleDelayNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic [7:0] data;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.data[3] <= ##1 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CycleDelayElab, SynchronousDriveWithCycleDelayNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.data <= ##1 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CycleDelayElab, GenerateBlockWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  if (1) begin : g\n"
      "    always begin\n"
      "      ##5;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 3, "14.11"));
}

TEST(CycleDelayElab, GenerateLoopWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i = i + 1) begin : g\n"
      "    always begin\n"
      "      ##5;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 3, "14.11"));
}

TEST(CycleDelayElab, IntraAssignCycleDelayInTaskErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  task t;\n"
      "    q = ##2 d;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 6, "14.11"));
}

TEST(CycleDelayElab, IntraAssignCycleDelayInFunctionErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  function void fn();\n"
      "    q = ##2 d;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 6, "14.11"));
}

TEST(CycleDelayElab, SynchronousDriveInTaskNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk;\n"
      "  logic data; default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  logic d;\n"
      "  task t;\n"
      "    cb.data <= ##2 d;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CycleDelayElab, ForkArmWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      ##5;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
}

TEST(CycleDelayElab, RandcaseItemWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: ##5;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
}

TEST(CycleDelayElab, AssertionPassStmtWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    assert (1) ##5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
}

TEST(CycleDelayElab, AssertionFailStmtWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    assert (1) else ##5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
}

TEST(CycleDelayElab, RandsequenceCodeBlockWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { ##5; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
}

TEST(CycleDelayElab, IntraAssignCycleDelayInForkArmErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] data, r;\n"
             "  default clocking cb @(posedge clk);\n"
             "    output data;\n"
             "  endclocking\n"
             "  initial begin\n"
             "    fork\n"
             "      r <= ##1 data;\n"
             "    join\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 9, "14.11"));
}

TEST(CycleDelayElab, PackageClassMethodErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pk;\n"
             "  class C;\n"
             "    task run; ##1; endtask\n"
             "  endclass\n"
             "endpackage\n"
             "module t;\n"
             "  import pk::*;\n"
             "  logic clk;\n"
             "  default clocking cb @(posedge clk);\n"
             "  endclocking\n"
             "  initial begin\n"
             "    static C h = new;\n"
             "    h.run();\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 3, "14.11"));
}

TEST(CycleDelayElab, PackageTaskAndNestedClassMethodError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package pk;\n"
             "  task automatic wait1; ##1; endtask\n"
             "  class O;\n"
             "    class I;\n"
             "      task go; ##2; endtask\n"
             "    endclass\n"
             "  endclass\n"
             "endpackage\n"
             "module t;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 2, "14.11"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) requires a default clocking block", 5, "14.11"));
}

TEST(CycleDelayElab, PackageWithoutCycleDelayNoError) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("package pk;\n"
             "  task automatic wait1; #1; endtask\n"
             "  class C;\n"
             "    task run; #1; endtask\n"
             "  endclass\n"
             "endpackage\n"
             "module t;\n"
             "endmodule\n",
             f));
}

TEST(CycleDelayElab, DriveThroughAnInterfaceClockingBlockPathTakesACycleDelay) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface SyncBus(input logic clk);\n"
      "  logic a, b, c;\n"
      "  clocking sb @(posedge clk);\n"
      "    input a; output b; inout c;\n"
      "  endclocking\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk = 0, a;\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  SyncBus b1(clk);\n"
      "  task automatic do_it(virtual SyncBus v); v.sb.c <= ##1 1; endtask\n"
      "  initial begin\n"
      "    b1.sb.c <= ##1 1;\n"
      "    do_it(b1);\n"
      "    a <= ##1 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 15, "14.11"));
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 11, "14.11"));
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "cycle delay (##) is not a legal intra-assignment delay", 13, "14.11"));
}

TEST(CycleDelayElab, NegativeConstantCycleDelayErrors) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  logic [7:0] q;\n"
             "  parameter int P = -2;\n"
             "  default clocking cb @(posedge clk);\n"
             "    output q;\n"
             "  endclocking\n"
             "  initial ##(-1) $display(\"a\");\n"
             "  initial ##(P) $display(\"b\");\n"
             "  initial cb.q <= ##(P) 1;\n"
             "  initial ##(P + 2) $display(\"c\");\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cycle delay (##) value is negative (-1)", 8,
                            "14.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cycle delay (##) value is negative (-2)", 9,
                            "14.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cycle delay (##) value is negative (-2)", 10,
                            "14.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "cycle delay (##) value", 11,
                             "14.11"));
}

TEST(CycleDelayElab, NestedModuleTakesTheEnclosingDefaultClocking) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  logic clk;\n"
             "  default clocking cb @(posedge clk); endclocking\n"
             "  module inner;\n"
             "    initial ##2 $display(\"x\");\n"
             "  endmodule\n"
             "  inner u();\n"
             "endmodule\n"));
}

TEST(CycleDelayElab, GenerateBlockDefaultClockingCountsInIt) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  if (1) begin : g\n"
             "    default clocking cb @(posedge clk); endclocking\n"
             "    initial ##2 $display(\"x\");\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
