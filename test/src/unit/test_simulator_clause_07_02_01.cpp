#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackedStructSimulation, PrimaryMemberAccess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] x;\n"
      "  initial begin p = 16'hABCD; x = p.hi; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// §7.2.1: First member is most significant, decreasing significance.
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

// §7.2.1: Packed struct used as a whole with bitwise operators.
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

// §7.2.1: Packed struct assigned from concatenation.
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

// §7.2.1: Packed struct can be bit-selected as packed array [n-1:0].
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

// §7.2.1: Member write then read back whole struct.
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
