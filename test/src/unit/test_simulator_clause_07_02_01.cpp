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
