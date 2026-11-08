#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

void RunAndCheck(
    const std::string& src,
    std::initializer_list<std::pair<const char*, uint64_t>> checks) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  LowerRunAndCheck(f, design, checks);
}

TEST(AssignmentWithinExpression, SimpleAssignUpdatesTargetAndReturnsValue) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] a, q;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    q = (a = 8'd42);\n"
      "  end\n"
      "endmodule\n",
      {{"a", 42u}, {"q", 42u}});
}

TEST(AssignmentWithinExpression, ChainedAssignPropagatesToEveryTarget) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'd0; b = 8'd0; c = 8'd0;\n"
      "    a = (b = (c = 8'd5));\n"
      "  end\n"
      "endmodule\n",
      {{"a", 5u}, {"b", 5u}, {"c", 5u}});
}

TEST(AssignmentWithinExpression, CompoundAddAssignReturnsUpdatedValue) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] x, q;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    q = (x += 8'd5);\n"
      "  end\n"
      "endmodule\n",
      {{"x", 15u}, {"q", 15u}});
}

TEST(AssignmentWithinExpression, ReturnedValueUsesLeftHandWidth) {
  RunAndCheck(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    q = (narrow = 8'hFF);\n"
      "  end\n"
      "endmodule\n",
      {{"narrow", 0xFu}, {"q", 0x0Fu}});
}

TEST(AssignmentWithinExpression, ReturnedValueFeedsOuterArithmetic) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] a, q;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    q = (a = 8'd10) + 8'd20;\n"
      "  end\n"
      "endmodule\n",
      {{"a", 10u}, {"q", 30u}});
}

TEST(AssignmentWithinExpression, ReturnedValueAsFalseIfCondition) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] a, q;\n"
      "  initial begin\n"
      "    q = 8'd0;\n"
      "    if ((a = 8'd0)) q = 8'd1; else q = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      {{"a", 0u}, {"q", 2u}});
}

TEST(AssignmentWithinExpression, ReturnedValueAsTrueIfCondition) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] a, q;\n"
      "  initial begin\n"
      "    q = 8'd0;\n"
      "    if ((a = 8'd7)) q = 8'd1; else q = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      {{"a", 7u}, {"q", 1u}});
}

TEST(AssignmentWithinExpression, ConcatTargetSplitsValueAndReturnsIt) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] hi, lo;\n"
      "  logic [31:0] q;\n"
      "  initial begin\n"
      "    q = ({hi, lo} = 16'hABCD);\n"
      "  end\n"
      "endmodule\n",
      {{"hi", 0xABu}, {"lo", 0xCDu}, {"q", 0x0000ABCDu}});
}

TEST(AssignmentWithinExpression, ConcatTargetResultIsUnsignedForSignedRhs) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] hi, lo;\n"
      "  logic signed [15:0] src;\n"
      "  logic [31:0] q;\n"
      "  initial begin\n"
      "    src = 16'hFFFF;\n"
      "    q = ({hi, lo} = src);\n"
      "  end\n"
      "endmodule\n",
      {{"hi", 0xFFu}, {"lo", 0xFFu}, {"q", 0x0000FFFFu}});
}

TEST(AssignmentWithinExpression, ConcatTargetResultWidthIsSumOfOperandWidths) {
  RunAndCheck(
      "module t;\n"
      "  logic [3:0] hi;\n"
      "  logic [7:0] lo;\n"
      "  logic [31:0] q;\n"
      "  initial begin\n"
      "    q = ({hi, lo} = 16'hFABC);\n"
      "  end\n"
      "endmodule\n",
      {{"hi", 0xAu}, {"lo", 0xBCu}, {"q", 0x00000ABCu}});
}

TEST(AssignmentWithinExpression, CompoundAssignToAnArrayElementUpdatesIt) {
  RunAndCheck(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int q;\n"
      "  initial begin\n"
      "    arr[2] = 10;\n"
      "    q = (arr[2] += 5);\n"
      "  end\n"
      "endmodule\n",
      {{"arr[2]", 15u}, {"q", 15u}});
}

TEST(AssignmentWithinExpression, CompoundAssignToABitSelectWritesOnlyThatBit) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic q;\n"
      "  initial begin\n"
      "    d = 8'h00;\n"
      "    q = (d[3] += 1'b1);\n"
      "  end\n"
      "endmodule\n",
      {{"d", 0x08u}, {"q", 1u}});
}

TEST(AssignmentWithinExpression,
     CompoundAssignToAPartSelectWritesOnlyThoseBits) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] q;\n"
      "  initial begin\n"
      "    d = 8'hF0;\n"
      "    q = (d[3:0] += 4'd3);\n"
      "  end\n"
      "endmodule\n",
      {{"d", 0xF3u}, {"q", 3u}});
}

TEST(AssignmentWithinExpression, CompoundAssignToAStructMemberUpdatesIt) {
  RunAndCheck(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0] hi;\n"
      "    logic [3:0] lo;\n"
      "  } pair_t;\n"
      "  pair_t s;\n"
      "  int q;\n"
      "  initial begin\n"
      "    s.hi = 4'd2;\n"
      "    s.lo = 4'd5;\n"
      "    q = (s.lo += 4'd3);\n"
      "  end\n"
      "endmodule\n",
      {{"s", 0x28u}, {"q", 8u}});
}

TEST(AssignmentWithinExpression,
     CompoundAssignToPartSelectYieldsTheSelectWidth) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    d = 8'h00;\n"
      "    q = (d[3:0] += 8'hFF);\n"
      "  end\n"
      "endmodule\n",
      {{"d", 0x0Fu}, {"q", 0x0Fu}});
}

TEST(AssignmentWithinExpression,
     CompoundAssignToArrayElementYieldsElementWidth) {
  RunAndCheck(
      "module t;\n"
      "  byte arr [0:3];\n"
      "  logic [15:0] q;\n"
      "  initial begin\n"
      "    arr[2] = 8'd10;\n"
      "    q = (arr[2] += 16'd300);\n"
      "  end\n"
      "endmodule\n",
      {{"q", 54u}});
}

TEST(AssignmentWithinExpression,
     CompoundAssignToQueueElementYieldsElementWidth) {
  RunAndCheck(
      "module t;\n"
      "  byte qu [$];\n"
      "  logic [15:0] q;\n"
      "  initial begin\n"
      "    qu.push_back(8'd10);\n"
      "    q = (qu[0] += 16'd300);\n"
      "  end\n"
      "endmodule\n",
      {{"q", 54u}});
}

TEST(AssignmentWithinExpression,
     CompoundAssignToStructMemberYieldsMemberWidth) {
  RunAndCheck(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t s;\n"
      "  logic [15:0] q;\n"
      "  initial begin\n"
      "    s = 16'h000A;\n"
      "    q = (s.lo += 16'd300);\n"
      "  end\n"
      "endmodule\n",
      {{"q", 54u}});
}

TEST(AssignInExprSim, ValueIsTheRightHandSideCastToTheTargetsType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  real r, y;\n"
                       "  int i, k;\n"
                       "  shortint s = -1;\n"
                       "  initial begin\n"
                       "    y = (r = 3) / 2;\n"
                       "    k = (i = 2.7);\n"
                       "    if ((i = s) < 0) $display(\"neg\");\n"
                       "    $display(\"%0g %0d\", y, k);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "neg\n1.5 3\n");
}

TEST(AssignmentWithinExpression, AssignToAStructMemberUpdatesItAndYieldsIt) {
  RunAndCheck(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t s;\n"
      "  logic [15:0] q;\n"
      "  initial begin\n"
      "    s = 16'h0A0A;\n"
      "    q = (s.lo = 16'd300);\n"
      "  end\n"
      "endmodule\n",
      {{"s", 0x0A2Cu}, {"q", 44u}});
}

TEST(AssignmentWithinExpression, AssignToAClassPropertyUpdatesTheObject) {
  RunAndCheck(
      "module t;\n"
      "  class C;\n"
      "    bit [7:0] v = 7;\n"
      "  endclass\n"
      "  C c;\n"
      "  int y, z;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    z = (c.v = -1);\n"
      "    y = c.v;\n"
      "  end\n"
      "endmodule\n",
      {{"y", 255u}, {"z", 255u}});
}

TEST(AssignmentWithinExpression,
     AssignThroughAPackageArrayElementReachesTheObject) {
  RunAndCheck(
      "package p;\n"
      "  class C;\n"
      "    int v = 7;\n"
      "  endclass\n"
      "  C objs[2];\n"
      "endpackage\n"
      "module t;\n"
      "  import p::*;\n"
      "  C c;\n"
      "  int y, z;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    p::objs[1] = c;\n"
      "    z = (p::objs[1].v = 5);\n"
      "    y = c.v;\n"
      "  end\n"
      "endmodule\n",
      {{"y", 5u}, {"z", 5u}});
}

}  // namespace
