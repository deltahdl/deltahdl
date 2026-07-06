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

// §7.3.1: a single bit of a packed union can be selected as if the union were a
// packed array (one-bit select, distinct from the part-select form).
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

// §7.3.1: an explicitly unsigned packed union zero-extends when read as a whole
// vector (the same result as the default, reached through the `unsigned`
// keyword rather than by omission).
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

// §7.3.1 + §7.4.1: a packed-array member (built from real §7.4.1
// multi-dimension syntax) aliases the same storage as a plain vector member, so
// a value written through one is read back through the other.
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

// §7.3.1: a packed union containing a 4-state member is 4-state, and reading a
// 2-state member implicitly converts 4-state to 2-state (x/z -> 0). Writing x
// into the logic member and reading through the bit member must yield 0, so the
// case-equality against 8'h00 (which distinguishes x from 0) holds.
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

// §7.3.1: the 4-state logic member of the same union preserves x/z (no
// conversion), so reading it back is not equal to a known 0 value.
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

// §7.3.1: writing a 2-state member of a 4-state packed union implicitly
// converts 2-state to 4-state, so the previously-unknown union bits it covers
// become known. After seeding the union with x through the logic member, a
// full-width write through the bit member leaves the 4-state member reading the
// known written value (case-equality against 8'h42 holds).
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

}  // namespace
