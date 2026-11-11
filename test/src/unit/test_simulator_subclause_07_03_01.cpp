#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackedUnionSimulation, CrossMemberReadBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a = 8'hA5;\n"
      "    result = u.b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xA5u);
}

TEST(PackedUnionSimulation, ArithmeticOnPackedUnion) {
  auto v = RunAndGet(
      "module t;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a = 8'd10;\n"
      "    result = u + 5;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 15u);
}

TEST(PackedUnionSimulation, BitSelectOnPackedUnion) {
  auto v = RunAndGet(
      "module t;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "  logic [3:0] result;\n"
      "  initial begin\n"
      "    u.a = 8'hA5;\n"
      "    result = u[3:0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x5u);
}

TEST(PackedUnionSimulation, SingleBitSelectOnPackedUnion) {
  auto v = RunAndGet(
      "module t;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a = 8'hA5;\n"
      "    result = u[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(PackedUnionSimulation, ExplicitUnsignedPackedUnion_ZeroExtends) {
  auto v = RunAndGet(
      "module t;\n"
      "  union packed unsigned { logic [7:0] a; logic [7:0] b; } u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a = 8'hFF;\n"
      "    result = u;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 255u);
}

TEST(PackedUnionSimulation, PackedArrayMemberReadBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  union packed {\n"
      "    logic [31:0] word;\n"
      "    logic [3:0][7:0] bytes;\n"
      "  } u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.word = 32'hDEADBEEF;\n"
      "    result = u.bytes;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xDEADBEEFu);
}

TEST(PackedUnionSimulation, DefaultUnsigned) {
  auto v = RunAndGet(
      "module t;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a = 8'hFF;\n"
      "    result = u;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 255u);
}

TEST(PackedUnionSimulation, SoftPackedUnionCrossMemberRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union soft packed {\n"
      "    logic [15:0] wide;\n"
      "    logic [7:0] narrow;\n"
      "  } su;\n"
      "  su u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.wide = 16'hABCD;\n"
      "    result = u.narrow;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xCDu);
}

TEST(PackedUnionSimulation, SoftPackedUnionMSBsUnaffected) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union soft packed {\n"
      "    logic [15:0] wide;\n"
      "    logic [7:0] narrow;\n"
      "  } su;\n"
      "  su u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.wide = 16'hFF00;\n"
      "    u.narrow = 8'h42;\n"
      "    result = u.wide;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xFF42u);
}

TEST(PackedUnionSimulation,
     NestedSoftPackedUnion_InnerNarrowWriteLeavesOuterUntouched) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union soft packed {\n"
      "    logic [11:0] inner_wide;\n"
      "    logic [3:0]  inner_narrow;\n"
      "  } inner_t;\n"
      "  typedef union soft packed {\n"
      "    logic [11:0] outer_wide;\n"
      "    inner_t      nested;\n"
      "  } outer_t;\n"
      "  outer_t u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.outer_wide      = 12'hABC;\n"
      "    u.nested.inner_narrow = 4'h5;\n"
      "    result = u.outer_wide;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xAB5u);
}

TEST(PackedUnionSimulation, TwoStateMemberRead_ConvertsFourStateToZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  union packed { logic [7:0] a; bit [7:0] b; } u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a = 8'bxxxxxxxx;\n"
      "    result = (u.b === 8'h00);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(PackedUnionSimulation, FourStateMemberRead_PreservesUnknown) {
  auto v = RunAndGet(
      "module t;\n"
      "  union packed { logic [7:0] a; bit [7:0] b; } u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a = 8'bxxxxxxxx;\n"
      "    result = (u.a === 8'h00);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(PackedUnionSimulation, TwoStateMemberWrite_ConvertsTwoStateToFourState) {
  auto v = RunAndGet(
      "module t;\n"
      "  union packed { logic [7:0] a; bit [7:0] b; } u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a = 8'bxxxxxxxx;\n"
      "    u.b = 8'h42;\n"
      "    result = (u.a === 8'h42);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(PackedUnionSimulation, WholeUnionAssignment_VisibleThroughMember) {
  auto v = RunAndGet(
      "module t;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = 8'h5A;\n"
      "    result = u.b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x5Au);
}

TEST(PackedUnionSimulation, PackedUnionSignedQualifier_SignExtendsOnAssign) {
  auto v = RunAndGet(
      "module t;\n"
      "  union packed signed { logic [7:0] a; logic [7:0] b; } u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.a = 8'hFF;\n"
      "    result = u;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xFFFFFFFFu);
}

TEST(PackedUnionSim, IndexOnAPackedArrayMemberSelectsAnElement) {
  const char* src =
      "module t;\n"
      "  typedef union packed { bit [15:0] w; bit [1:0][7:0] b; } u_t;\n"
      "  typedef struct packed { bit [3:0][3:0] n; bit [7:0] t; } s_t;\n"
      "  u_t u;\n"
      "  s_t s;\n"
      "  int b0, b1, n3, n0;\n"
      "  initial begin\n"
      "    u.w = 16'h1234;\n"
      "    s = 24'hABCD12;\n"
      "    b0 = u.b[0];\n"
      "    b1 = u.b[1];\n"
      "    n3 = s.n[3];\n"
      "    n0 = s.n[0];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "b0"), 0x34u);
  EXPECT_EQ(RunAndGet(src, "b1"), 0x12u);
  EXPECT_EQ(RunAndGet(src, "n3"), 0xAu);
  EXPECT_EQ(RunAndGet(src, "n0"), 0xDu);
}

TEST(PackedUnionSimulation, AnInPlaceUnionsStateIsItsMembers) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  function automatic union packed {logic [3:0] a; "
                       "logic [3:0] b;} fl(input union packed {logic [3:0] a; "
                       "logic [3:0] b;} x);\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "  function automatic union packed {bit [3:0] a; "
                       "bit [3:0] b;} fb(input union packed {bit [3:0] a; "
                       "bit [3:0] b;} x);\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "  initial $display(\"%b %b\", fl(4'b1x0z), "
                       "fb(4'b1x0z));\n"
                       "endmodule\n",
                       f),
            "1x0z 1000\n");
}

TEST(PackedUnionSimulation, AnInPlaceUnionOfATypedefMemberTakesItsState) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef logic [3:0] n4_t;\n"
                       "module t;\n"
                       "  typedef bit [3:0] b4_t;\n"
                       "  function automatic void fl(union packed {n4_t a; "
                       "n4_t b;} u);\n"
                       "    $display(\"%b\", u);\n"
                       "  endfunction\n"
                       "  function automatic void fb(union packed {b4_t a; "
                       "b4_t b;} u);\n"
                       "    $display(\"%b\", u);\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    fl(4'b1x0z);\n"
                       "    fb(4'b1x0z);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1x0z\n1000\n");
}

TEST(PackedUnionSimulation, SoftPackedUnionLaysOutNestedMembersRightJustified) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef union soft packed {\n"
                 "    struct packed { bit [4:0] valA, valB, valC; } D1;\n"
                 "    struct packed {\n"
                 "      bit [1:0] valX;\n"
                 "      union soft { bit [9:0] F1; bit [7:0] F2; } valY;\n"
                 "    } D2;\n"
                 "  } Data_u;\n"
                 "  Data_u d;\n"
                 "  initial begin\n"
                 "    $display(\"%0d %0d\", $bits(Data_u), $bits(d.D2));\n"
                 "    d = 0; d.D2.valX = 2'b11; d.D2.valY.F1 = 10'h3FF;\n"
                 "    $display(\"%b\", d);\n"
                 "    d = 0; d.D2.valY.F2 = 8'hFF;\n"
                 "    $display(\"%h\", d);\n"
                 "    d = 0; d.D1.valA = 5'h1F;\n"
                 "    $display(\"%b %b\", d.D2.valX, d.D2.valY.F1);\n"
                 "    d = '1; d.D2.valY.F2 = 8'h00;\n"
                 "    $display(\"%b\", d);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "15 12\n000111111111111\n00ff\n11 0000000000\n111111100000000\n");
}

TEST(PackedUnionSimulation, PackedUnionIsAVectorToBitwiseAndLogicalOperators) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  union packed { logic [7:0] a; logic [7:0] b; } u, w;\n"
                 "  initial begin\n"
                 "    u.a = 8'hF0; w.b = 8'h3C;\n"
                 "    $display(\"%h %h %h %h %b %b %b %b\", u & w, u | w, "
                 "u ^ w, ~u, !u, u && w, u == w, u[7:4] == 4'hF);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "30 fc cc 0f 0 1 0 1\n");
}

TEST(PackedUnionSimulation, SignednessOfAPackedUnionDecidesComparison) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  union packed signed { bit [7:0] a; bit [7:0] b; } s;\n"
                 "  union packed { bit [7:0] a; bit [7:0] b; } u;\n"
                 "  initial begin\n"
                 "    s.a = 8'hFF; u.a = 8'hFF;\n"
                 "    $display(\"%b %b %0d %0d\", s < 0, u < 0, s, u);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1 0 -1 255\n");
}

}  // namespace
