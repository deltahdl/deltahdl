#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

struct SimCh9Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh9Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// ---------------------------------------------------------------------------
// 1. always_comb executes at time 0 (initial evaluation).
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombExecutesAtTimeZero) {
  SimCh9Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial a = 8'd0;\n"
      "  always_comb begin\n"
      "    result = a + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // a is explicitly 0, so result = 0 + 1 = 1.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 2. always_comb AND gate: result = a & b.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombAndGate) {
  SimCh9Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h3C;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a & b;\n"
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
// 3. always_comb OR gate: result = a | b.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombOrGate) {
  SimCh9Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h0F;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// ---------------------------------------------------------------------------
// 4. always_comb XOR gate: result = a ^ b.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombXorGate) {
  SimCh9Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'h55;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a ^ b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// ---------------------------------------------------------------------------
// 5. always_comb NOT gate: result = ~a & mask.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombNotGate) {
  SimCh9Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'h0F;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = (~a) & 8'hFF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
}

// ---------------------------------------------------------------------------
// 6. always_comb 2-to-1 mux using if-else.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombMuxIfElse) {
  SimCh9Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "  end\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      result = a;\n"
      "    else\n"
      "      result = b;\n"
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
// 7. always_comb if-else selects the else branch.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombIfElseBranch) {
  SimCh9Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "  end\n"
      "  always_comb begin\n"
      "    if (sel)\n"
      "      result = a;\n"
      "    else\n"
      "      result = b;\n"
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
// 8. always_comb case statement decode.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombCaseDecode) {
  SimCh9Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 2'd2;\n"
      "  always_comb begin\n"
      "    case (sel)\n"
      "      2'd0: result = 8'd10;\n"
      "      2'd1: result = 8'd20;\n"
      "      2'd2: result = 8'd30;\n"
      "      2'd3: result = 8'd40;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

// ---------------------------------------------------------------------------
// 9. always_comb case with default branch.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombCaseDefault) {
  SimCh9Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 3'd7;\n"
      "  always_comb begin\n"
      "    case (sel)\n"
      "      3'd0: result = 8'd1;\n"
      "      3'd1: result = 8'd2;\n"
      "      default: result = 8'hFF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// ---------------------------------------------------------------------------
// 10. Two always_comb blocks in the same module.
// ---------------------------------------------------------------------------
TEST(SimCh9, MultipleAlwaysCombBlocks) {
  SimCh9Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, sum, diff;\n"
      "  initial begin\n"
      "    a = 8'd15;\n"
      "    b = 8'd5;\n"
      "  end\n"
      "  always_comb begin\n"
      "    sum = a + b;\n"
      "  end\n"
      "  always_comb begin\n"
      "    diff = a - b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s = f.ctx.FindVariable("sum");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->value.ToUint64(), 20u);
  auto* d = f.ctx.FindVariable("diff");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->value.ToUint64(), 10u);
}

// ---------------------------------------------------------------------------
// 11. Nested if-else priority encoding.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombPriorityEncoder) {
  SimCh9Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial a = 8'd15;\n"
      "  always_comb begin\n"
      "    if (a > 8'd20)\n"
      "      result = 8'd3;\n"
      "    else if (a > 8'd10)\n"
      "      result = 8'd2;\n"
      "    else if (a > 8'd5)\n"
      "      result = 8'd1;\n"
      "    else\n"
      "      result = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // a=15: a>20 false, a>10 true, so result=2.
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// ---------------------------------------------------------------------------
// 12. Multiple outputs from one always_comb block.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombMultipleOutputs) {
  SimCh9Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] doubled, incremented;\n"
      "  initial a = 8'd25;\n"
      "  always_comb begin\n"
      "    doubled = a << 1;\n"
      "    incremented = a + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* dbl = f.ctx.FindVariable("doubled");
  ASSERT_NE(dbl, nullptr);
  EXPECT_EQ(dbl->value.ToUint64(), 50u);
  auto* inc = f.ctx.FindVariable("incremented");
  ASSERT_NE(inc, nullptr);
  EXPECT_EQ(inc->value.ToUint64(), 26u);
}

// ---------------------------------------------------------------------------
// 13. Bit-select in always_comb using initial begin/end.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombBitSelect) {
  SimCh9Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'b0000_0100;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a >> 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // a = 4, a >> 2 = 1.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 14. Part-select via mask in always_comb (lower nibble).
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombPartSelect) {
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
  SimCh9Fixture f;
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
