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

TEST(PackedUnionSimulation, SoftPackedUnionNarrowMemberLandsAtLSB) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union soft packed {\n"
      "    logic [15:0] wide;\n"
      "    logic [7:0] narrow;\n"
      "  } su;\n"
      "  su u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u.wide = 16'h0000;\n"
      "    u.narrow = 8'hC3;\n"
      "    result = u.wide;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x00C3u);
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

}  // namespace
