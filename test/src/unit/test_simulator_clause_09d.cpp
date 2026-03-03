// Non-LRM tests

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// 23. always @* with case decode (address decoder pattern).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarCaseDecode) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] addr;\n"
      "  logic [3:0] sel;\n"
      "  always @*\n"
      "    case (addr)\n"
      "      2'b00: sel = 4'b0001;\n"
      "      2'b01: sel = 4'b0010;\n"
      "      2'b10: sel = 4'b0100;\n"
      "      2'b11: sel = 4'b1000;\n"
      "    endcase\n"
      "  initial begin\n"
      "    addr = 2'b11;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* sel = f.ctx.FindVariable("sel");
  ASSERT_NE(sel, nullptr);
  // addr = 2'b11, so sel = 4'b1000 = 8.
  EXPECT_EQ(sel->value.ToUint64(), 8u);
}

// ---------------------------------------------------------------------------
// 24. Multiple always @* blocks have independent sensitivity and outputs.
// ---------------------------------------------------------------------------
TEST(SimCh9d, MultipleAlwaysStarIndependent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d, x, y;\n"
      "  always @* x = a & b;\n"
      "  always @* y = c | d;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'h0F;\n"
      "    c = 8'hA0;\n"
      "    d = 8'h05;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* x = f.ctx.FindVariable("x");
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x0Fu);
  EXPECT_EQ(y->value.ToUint64(), 0xA5u);
}

// ---------------------------------------------------------------------------
// 25. always @* equivalent to always_comb for simple combinational logic.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarEquivAlwaysComb) {
  SimFixture f_star;
  auto* d_star = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @* y = a ^ b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'h55;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f_star);
  ASSERT_NE(d_star, nullptr);

  Lowerer lowerer_star(f_star.ctx, f_star.arena, f_star.diag);
  lowerer_star.Lower(d_star);
  f_star.scheduler.Run();

  SimFixture f_comb;
  auto* d_comb = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = a ^ b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'h55;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f_comb);
  ASSERT_NE(d_comb, nullptr);

  Lowerer lowerer_comb(f_comb.ctx, f_comb.arena, f_comb.diag);
  lowerer_comb.Lower(d_comb);
  f_comb.scheduler.Run();

  auto* y_star = f_star.ctx.FindVariable("y");
  auto* y_comb = f_comb.ctx.FindVariable("y");
  ASSERT_NE(y_star, nullptr);
  ASSERT_NE(y_comb, nullptr);
  EXPECT_EQ(y_star->value.ToUint64(), y_comb->value.ToUint64());
}

// ---------------------------------------------------------------------------
// 26. always @* with type cast (signed').
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarTypeCast) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [31:0] y;\n"
      "  always @* y = signed'(a);\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // 8'hFF sign-extended to 32 bits = 0xFFFFFFFF.
  EXPECT_EQ(y->value.ToUint64(), 0xFFFFFFFFu);
}

// ---------------------------------------------------------------------------
// 27. Verify correctness of combinational output set via initial block.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarCombOutputFromInitial) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b, y;\n"
      "  always @* y = a + b;\n"
      "  initial begin\n"
      "    a = 16'h1234;\n"
      "    b = 16'h4321;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x5555u);
}

// ---------------------------------------------------------------------------
// 28. Verify .width and .ToUint64() on always @* results (8-bit output).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarResultWidthAndValue8) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, y;\n"
      "  always @* y = a;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.width, 8u);
  EXPECT_EQ(y->value.ToUint64(), 0xABu);
}

// ---------------------------------------------------------------------------
// 29. Verify .width and .ToUint64() on always @(*) results (32-bit output).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarParenResultWidth32) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, y;\n"
      "  always @(*) y = a;\n"
      "  initial begin\n"
      "    a = 32'hDEADBEEF;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.width, 32u);
  EXPECT_EQ(y->value.ToUint64(), 0xDEADBEEFu);
}

// ---------------------------------------------------------------------------
// 30. always @* with logical NOT (!) on a multi-bit signal.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarLogicalNot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic y;\n"
      "  always @* y = !a;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // !0 = 1.
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

}  // namespace
