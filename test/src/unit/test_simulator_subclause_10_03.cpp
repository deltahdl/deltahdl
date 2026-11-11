#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ContinuousAssignSim, ContAssignExecutes) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [31:0] y;\n"
      "  assign y = 99;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(ContinuousAssignSim, DrivesScalarNet) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ContinuousAssignSim, DrivesScalarVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic v;\n"
      "  assign v = 1'b1;\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ContinuousAssignSim, DrivesVectorVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] v;\n"
      "  assign v = 16'hBEEF;\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBEEFu);
}

TEST(ContinuousAssignSim, AssignmentReevaluatesOnRhsChange) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  wire  [7:0] y;\n"
      "  assign y = a + b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = 8'd2;\n"
      "    #1;\n"
      "    a = 8'd40;\n"
      "    b = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 42u);
}

TEST(ContinuousAssignSim, RhsBitSelectOfAPackedVectorTracksLaterChanges) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  wire y;\n"
      "  assign y = a[1];\n"
      "  initial begin\n"
      "    a = 4'b0010;\n"
      "    #1;\n"
      "    a = 4'b0000;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
}

TEST(ContinuousAssignSim, ProgramContinuousAssignmentsDriveANetAndAVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p;\n"
                       "  logic a = 1; wire w; logic v;\n"
                       "  assign w = a;\n"
                       "  assign v = ~a;\n"
                       "  initial begin\n"
                       "    #1 $display(\"%b %b\", w, v);\n"
                       "    a = 0;\n"
                       "    #1 $display(\"%b %b\", w, v);\n"
                       "  end\n"
                       "endprogram\n",
                       f),
            "1 0\n0 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ContinuousAssignSim, InterfaceContinuousAssignmentsDriveANetAndAVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface i;\n"
                       "  logic a = 1; wire w; logic v;\n"
                       "  assign w = a;\n"
                       "  assign v = ~a;\n"
                       "endinterface\n"
                       "module t;\n"
                       "  i u();\n"
                       "  initial begin\n"
                       "    #1 $display(\"%b %b\", u.w, u.v);\n"
                       "    u.a = 0;\n"
                       "    #1 $display(\"%b %b\", u.w, u.v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 0\n0 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ContinuousAssignSim, CheckerContinuousAssignmentDrivesAVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("checker c(logic a);\n"
                       "  logic v;\n"
                       "  assign v = ~a;\n"
                       "endchecker\n"
                       "module t;\n"
                       "  logic a = 1;\n"
                       "  c u(a);\n"
                       "  initial begin\n"
                       "    #1 $display(\"%b\", u.v);\n"
                       "    a = 0;\n"
                       "    #1 $display(\"%b\", u.v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0\n1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
