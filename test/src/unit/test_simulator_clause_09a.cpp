// Non-LRM tests

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// 14. Part-select via mask in always_comb (lower nibble).
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombPartSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a & 8'h0F;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

// ---------------------------------------------------------------------------
// 15. Upper part-select via shift in always_comb (upper nibble).
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombUpperPartSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = (a >> 4) & 8'h0F;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

// ---------------------------------------------------------------------------
// 16. Concatenation in always_comb.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombConcatenation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] hi, lo;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    hi = 4'hA;\n"
      "    lo = 4'hB;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = {hi, lo};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// ---------------------------------------------------------------------------
// 17. Ternary operator in always_comb.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombTernaryTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 1;\n"
      "  always_comb begin\n"
      "    result = sel ? 8'd42 : 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// ---------------------------------------------------------------------------
// 18. Ternary operator in always_comb (false branch).
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombTernaryFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 0;\n"
      "  always_comb begin\n"
      "    result = sel ? 8'd42 : 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// ---------------------------------------------------------------------------
// 19. Function call in always_comb.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombFunctionCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function automatic logic [7:0] add_one(input logic [7:0] x);\n"
      "    return x + 8'd1;\n"
      "  endfunction\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'd9;\n"
      "  always_comb begin\n"
      "    result = add_one(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// ---------------------------------------------------------------------------
// 20. Verify result variable width is 8 bits.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombResultWidth8) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'd5;\n"
      "  always_comb begin\n"
      "    result = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// ---------------------------------------------------------------------------
// 21. Verify result variable width is 32 bits (int).
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombResultWidth32) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  int result;\n"
      "  initial a = 100;\n"
      "  always_comb begin\n"
      "    result = a * 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 200u);
}

// ---------------------------------------------------------------------------
// 22. always_comb with packed struct assignment.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombStructAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] upper;\n"
      "    logic [7:0] lower;\n"
      "  } pair_t;\n"
      "  pair_t p;\n"
      "  logic [15:0] result;\n"
      "  initial p = 16'hCAFE;\n"
      "  always_comb begin\n"
      "    result = p;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

// ---------------------------------------------------------------------------
// 23. always_comb with struct field access.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombStructFieldAccess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] hi;\n"
      "    logic [7:0] lo;\n"
      "  } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] result;\n"
      "  initial p = 16'hABCD;\n"
      "  always_comb begin\n"
      "    result = p.lo;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

// ---------------------------------------------------------------------------
// 24. always_comb with addition and subtraction.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombAddSub) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'd100;\n"
      "    b = 8'd37;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a - b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 63u);
}

// ---------------------------------------------------------------------------
// 25. always_comb with logical operators.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombLogicalOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 0;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a && !b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 26. always_comb with shift operations.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombShift) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'b0000_0011;\n"
      "  always_comb begin\n"
      "    result = a << 4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x30u);
}

// ---------------------------------------------------------------------------
// 27. always_comb with comparison producing boolean.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombComparison) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd5;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = (a > b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 28. always_comb with explicit zero inputs produces zero output.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombExplicitZeros) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    b = 8'd0;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a | b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // Both a and b explicitly 0, so result = 0 | 0 = 0.
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// ---------------------------------------------------------------------------
// 29. always_comb with chained ternary (nested conditional).
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombChainedTernary) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 2'd1;\n"
      "  always_comb begin\n"
      "    result = (sel == 2'd0) ? 8'd10 :\n"
      "             (sel == 2'd1) ? 8'd20 :\n"
      "             (sel == 2'd2) ? 8'd30 : 8'd40;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// ---------------------------------------------------------------------------
// 30. always_comb with reduction operator and width check.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombReductionAnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic result;\n"
      "  initial a = 4'b1111;\n"
      "  always_comb begin\n"
      "    result = &a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
