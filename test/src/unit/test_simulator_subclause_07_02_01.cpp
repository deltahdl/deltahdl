#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackedStructSimulation, MsbFirstBitOrdering_ThreeFields) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "    logic [7:0] c;\n"
      "  } tri_t;\n"
      "  tri_t s;\n"
      "  logic [7:0] ra, rb, rc;\n"
      "  initial begin\n"
      "    s = 24'hAA_BB_CC;\n"
      "    ra = s.a;\n"
      "    rb = s.b;\n"
      "    rc = s.c;\n"
      "  end\n"
      "endmodule\n",
      "ra");
  EXPECT_EQ(v, 0xAAu);
}

TEST(PackedStructSimulation, MsbFirstBitOrdering_MiddleField) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "    logic [7:0] c;\n"
      "  } tri_t;\n"
      "  tri_t s;\n"
      "  logic [7:0] rb;\n"
      "  initial begin s = 24'hAA_BB_CC; rb = s.b; end\n"
      "endmodule\n",
      "rb");
  EXPECT_EQ(v, 0xBBu);
}

TEST(PackedStructSimulation, MsbFirstBitOrdering_LeastSignificantField) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "    logic [7:0] c;\n"
      "  } tri_t;\n"
      "  tri_t s;\n"
      "  logic [7:0] rc;\n"
      "  initial begin s = 24'hAA_BB_CC; rc = s.c; end\n"
      "endmodule\n",
      "rc");
  EXPECT_EQ(v, 0xCCu);
}

TEST(PackedStructSimulation, ArithmeticAdditionOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t a, b;\n"
      "  logic [15:0] z;\n"
      "  initial begin\n"
      "    a = 16'h0102;\n"
      "    b = 16'h0304;\n"
      "    z = a + b;\n"
      "  end\n"
      "endmodule\n",
      "z");
  EXPECT_EQ(v, 0x0406u);
}

TEST(PackedStructSimulation, BitwiseAndOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } w_t;\n"
      "  w_t x, y;\n"
      "  logic [15:0] z;\n"
      "  initial begin\n"
      "    x = 16'hFF0F;\n"
      "    y = 16'h0F0F;\n"
      "    z = x & y;\n"
      "  end\n"
      "endmodule\n",
      "z");
  EXPECT_EQ(v, 0x0F0Fu);
}

TEST(PackedStructSimulation, AssignFromConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic [7:0] rhi;\n"
      "  initial begin w = {8'hAB, 8'hCD}; rhi = w.hi; end\n"
      "endmodule\n",
      "rhi");
  EXPECT_EQ(v, 0xABu);
}

TEST(PackedStructSimulation, PartSelectOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic [7:0] top_byte;\n"
      "  initial begin w = 16'hABCD; top_byte = w[15:8]; end\n"
      "endmodule\n",
      "top_byte");
  EXPECT_EQ(v, 0xABu);
}

TEST(PackedStructSimulation, SingleBitSelectOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic msb;\n"
      "  initial begin w = 16'h8000; msb = w[15]; end\n"
      "endmodule\n",
      "msb");
  EXPECT_EQ(v, 1u);
}

TEST(PackedStructSimulation, WriteTwoStateValueToBitMember_OverwritesPriorX) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { bit [7:0] b; logic [7:0] l; } mixed_t;\n"
      "  mixed_t s;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    s = 16'bxxxxxxxx_00000000;\n"
      "    s.b = 8'hA5;\n"
      "    r = s.b;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xA5u);
}

TEST(PackedStructSimulation, BitMemberInFourStateStruct_ReadsAsTwoState) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { bit [7:0] b; logic [7:0] l; } mixed_t;\n"
      "  mixed_t s;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    s = 16'bxxxxxxxx_00000000;\n"
      "    r = s.b;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0u);
}

// §7.2.1: a packed structure used as a whole behaves per its signedness. A
// 'packed signed' struct read as a single vector sign-extends when widened, so
// an all-ones 8-bit value fills the upper byte with ones.
TEST(PackedStructSimulation, SignedPackedStructWholeReadSignExtends) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed signed { logic [7:0] a; } b_t;\n"
      "  b_t s;\n"
      "  logic [15:0] r;\n"
      "  initial begin s = 8'hFF; r = s; end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xFFFFu);
}

// §7.2.1: unsigned is the default signedness of a packed structure, so the
// same whole-vector read zero-extends when widened. This discriminates the
// default from the explicit 'signed' case above.
TEST(PackedStructSimulation, UnsignedDefaultPackedStructWholeReadZeroExtends) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; } b_t;\n"
      "  b_t s;\n"
      "  logic [15:0] r;\n"
      "  initial begin s = 8'hFF; r = s; end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0x00FFu);
}

// §7.2.1 built from §6.11 integer data types: a packed structure whose members
// are declared with real Table 6-8 types (int, byte) packs them without gaps in
// most-significant-first order. Driven end-to-end (parse/elaborate/run), the
// first member occupies the high bits of the whole vector.
TEST(PackedStructSimulation, IntegerTypeMembersPackMsbFirst) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { int a; byte b; } m_t;\n"
      "  m_t m;\n"
      "  logic [31:0] ra;\n"
      "  initial begin m = 40'h1122334455; ra = m.a; end\n"
      "endmodule\n",
      "ra");
  EXPECT_EQ(v, 0x11223344u);
}

// §7.2.1: bits of a packed structure may be selected as if it were a packed
// array [n-1:0]. This exercises the indexed part-select form ([base+:width]),
// distinct from the fixed [msb:lsb] and single-bit select forms.
TEST(PackedStructSimulation, IndexedPartSelectOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic [7:0] top_byte;\n"
      "  initial begin w = 16'hABCD; top_byte = w[8+:8]; end\n"
      "endmodule\n",
      "top_byte");
  EXPECT_EQ(v, 0xABu);
}

TEST(PackedStructSimulation, MemberWriteUpdatesWholeVector) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    w = 16'h0000;\n"
      "    w.hi = 8'hAB;\n"
      "    result = w;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xAB00u);
}

}  // namespace
