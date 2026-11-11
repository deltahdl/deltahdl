#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(AssignmentLeftHandForms, ContinuousAssignmentDrivesEveryListedForm) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t; logic a = 1; logic [2:0] b = 3'b101, c = 3'b011;\n"
          "  wire n; wire [2:0] nw; wire [7:0] nv;\n"
          "  logic v; logic [2:0] vw; logic [7:0] pv;\n"
          "  assign n = a; assign nw = b; assign v = a; assign vw = c;\n"
          "  assign nv[0] = a; assign nv[4:2] = b;\n"
          "  assign {nv[7], {nv[6:5], nv[1]}} = 4'b1010;\n"
          "  assign pv[1] = a; assign pv[6:4] = c;\n"
          "  assign {pv[7], {pv[3:2], pv[0]}} = 4'b0101;\n"
          "  initial begin\n"
          "    #1 $display(\"%b %b %b %b %b %b\", n, nw, v, vw, nv, pv);\n"
          "    a = 0;\n"
          "    #1 $display(\"%b %b %b %b\", n, v, nv, pv);\n"
          "  end\n"
          "endmodule\n",
          f),
      "1 101 1 011 10110101 00111011\n"
      "0 0 10110100 00111001\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentLeftHandForms, ProceduralAssignmentWritesEveryListedForm) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t; logic s; logic [7:0] pv; logic [7:0] mem [0:3];\n"
                 "  int arr [0:3], arr2 [0:3]; int m2 [0:1][0:1];\n"
                 "  logic [3:0] u, w; logic s2;\n"
                 "  initial begin\n"
                 "    s = 1; pv = 8'h00; pv[2] = 1'b1; pv[7:5] = 3'b101;\n"
                 "    mem[1] = 8'hA5; arr = '{1, 2, 3, 4}; arr2 = arr;\n"
                 "    arr2[0] = 9; arr2[2:3] = arr[0:1]; m2[1][0] = 7;\n"
                 "    {u, {s2, w}} = 9'b1010_1_0110;\n"
                 "    {pv[1:0], {s2, w[2:1]}} = 5'b10_0_00;\n"
                 "    $display(\"%b %b %h %p %p %0d\", s, pv, mem[1], arr,\n"
                 "             arr2, m2[1][0]);\n"
                 "    $display(\"%b %b %b\", u, s2, w);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1 10100110 a5 '{1, 2, 3, 4} '{9, 2, 1, 2} 7\n"
      "1010 0 0000\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentLeftHandForms,
     DISABLED_BlockingConcatenationWritesASelectOfAMemoryWord) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; logic [1:0] pv = 0; logic [7:0] mem [0:3];\n"
                       "  initial begin\n"
                       "    {pv, mem[1][3:0]} = 6'b11_1010;\n"
                       "    {pv[0], mem[2][5]} = 2'b01;\n"
                       "    $display(\"%b %h %b\", pv, mem[1], mem[2]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "10 xa xx1xxxxx\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentLeftHandForms,
     DISABLED_BlockingConcatenationWritesAMultidimensionalArrayElement) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t; logic [1:0] pv = 0; logic [7:0] m2 [0:1][0:1];\n"
                 "  initial begin\n"
                 "    {pv, m2[1][0]} = 10'h3AB;\n"
                 "    $display(\"%b %h %h\", pv, m2[1][0], m2[0][1]);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "11 ab xx\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentLeftHandForms,
     NonblockingConcatenationWritesAMultidimensionalArrayElement) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t; logic [1:0] pw = 0; logic [7:0] m2 [0:1][0:1];\n"
                 "  initial begin\n"
                 "    {pw, m2[1][0]} <= 10'h1AB;\n"
                 "    #1 $display(\"%b %h %h\", pw, m2[1][0], m2[0][1]);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "01 ab xx\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentLeftHandForms,
     DISABLED_NonblockingConcatenationWritesASelectOfAMemoryWord) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; logic [1:0] pv = 0; logic [7:0] mem [0:3];\n"
                       "  initial begin\n"
                       "    {pv, mem[1][3:0]} <= 6'b10_1010;\n"
                       "    #1 $display(\"%b %h\", pv, mem[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "10 xa\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentLeftHandForms, ContinuousConcatenationOfArrayElementSelects) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t; wire [7:0] nm [0:1]; wire n2;\n"
                 "  logic [7:0] vm [0:1]; logic v2;\n"
                 "  assign {nm[1][3:0], n2} = 5'b1011_1;\n"
                 "  assign {vm[1][3:0], v2} = 5'b0110_1;\n"
                 "  initial #1 $display(\"%b %b %b %b\", nm[1], n2, vm[1], "
                 "v2);\n"
                 "endmodule\n",
                 f),
      "zzzz1011 1 xxxx0110 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProceduralAssignmentHold, AVariableHoldsItsValueUntilTheNextAssignment) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; logic [3:0] r, q, src;\n"
                       "  initial begin\n"
                       "    src = 3; r = src; q <= src; src = 7;\n"
                       "    #5 $display(\"%0d %0d %0d\", r, q, src);\n"
                       "    r = src; q <= 9;\n"
                       "    #1 $display(\"%0d %0d\", r, q);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3 3 7\n"
            "7 9\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentDelayTimeUnit,
     DISABLED_StatementDelayWithATimeUnitScalesToTheModuleUnit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; timeunit 100ps; timeprecision 10ps;\n"
                       "  logic a = 1, r;\n"
                       "  initial #5 a = 0;\n"
                       "  initial begin #1ns r = a; $display(\"%0t %0d\", "
                       "$time, r); end\n"
                       "endmodule\n",
                       f),
            "10 0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentDelayTimeUnit,
     DISABLED_BlockingIntraAssignmentDelayWithATimeUnitScalesToTheModuleUnit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; timeunit 100ps; timeprecision 10ps;\n"
                       "  logic a = 1, r;\n"
                       "  initial #5 a = 0;\n"
                       "  initial begin r = #1ns a; $display(\"%0t %0d\", "
                       "$time, r); end\n"
                       "endmodule\n",
                       f),
            "10 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentDelayTimeUnit,
     NonblockingIntraAssignmentDelayWithATimeUnitScalesToTheModuleUnit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; timeunit 100ps; timeprecision 10ps;\n"
                       "  logic a = 1, r;\n"
                       "  initial #5 a = 0;\n"
                       "  initial begin\n"
                       "    r <= #1ns a; $display(\"%0t\", $time);\n"
                       "    #9 $display(\"%b\", r); #2 $display(\"%b\", r);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0\nx\n1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentDelayTimeUnit,
     ContinuousAssignmentDelayWithATimeUnitScalesToTheModuleUnit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; timeunit 100ps; timeprecision 10ps;\n"
                       "  wire [3:0] sum; logic [3:0] a = 0, b = 0;\n"
                       "  assign #2.5ns sum = a + b;\n"
                       "  initial begin\n"
                       "    #10 a = 1;\n"
                       "    wait (sum == 1) $display(\"%0.1f\", $realtime);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "35.0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentDelayTimeUnit,
     ContinuousAssignmentDelayWithATimeUnitRoundsToThePrecision) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; timeunit 1ns; timeprecision 1ns;\n"
                       "  wire [3:0] sum; logic [3:0] a = 0, b = 0;\n"
                       "  assign #2.5ns sum = a + b;\n"
                       "  initial begin\n"
                       "    #1 a = 1;\n"
                       "    wait (sum == 1) $display(\"%0t\", $time);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "4\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentDelayTimeUnit, EachFormWithTheModuleUnitGivesTheBareCount) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t; timeunit 1ns; timeprecision 1ns;\n"
                 "  logic a = 1, r1, r2, r3; wire [3:0] sum;\n"
                 "  logic [3:0] x = 0, y = 0;\n"
                 "  assign #2ns sum = x + y;\n"
                 "  initial #5 a = 0;\n"
                 "  initial begin #3ns r1 = a; $display(\"A %0t %0d\", $time, "
                 "r1); end\n"
                 "  initial begin r2 = #1ns a; $display(\"B %0t %0d\", $time, "
                 "r2); end\n"
                 "  initial begin r3 <= #6ns a; #4 $display(\"C %b\", r3); "
                 "end\n"
                 "  initial begin #10 x = 1; wait (sum == 1) "
                 "$display(\"D %0t\", $time); end\n"
                 "endmodule\n",
                 f),
      "B 1 1\nA 3 1\nC x\nD 12\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
