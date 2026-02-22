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

struct SimCh9bFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimCh9bFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// =============================================================================
// IEEE 1800 LRM section 9.2.2.2 -- always_comb compared with always @*
//
// Key behavioral properties of always_comb:
//   - Executes once at time 0 automatically (initial evaluation).
//   - Automatically infers a complete sensitivity list from signals read.
//   - Re-triggers whenever any read signal changes.
//   - No blocking timing controls allowed inside.
//   - Produces combinational logic: AND, OR, XOR, if-else, case, etc.
//
// Contrast with always @*:
//   - Does NOT execute at time 0; waits for the first event.
//   - The @* is consumed by the parser; in this implementation, always @*
//     maps to a plain always loop (no implicit suspension).
// =============================================================================

// ---------------------------------------------------------------------------
// 1. always_comb with constant assignment executes at time 0.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombConstAssignTime0) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [31:0] y;\n"
                              "  always_comb y = 42;\n"
                              "  initial #1 $finish;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 42u);
}

// ---------------------------------------------------------------------------
// 2. always_comb with zero assignment executes at time 0.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombZeroAssignTime0) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [31:0] y;\n"
                              "  always_comb y = 0;\n"
                              "  initial #1 $finish;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
}

// ---------------------------------------------------------------------------
// 3. always_comb AND gate: re-evaluates after input is set.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombAndGate) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, y;\n"
                              "  always_comb y = a & b;\n"
                              "  initial begin\n"
                              "    a = 8'hF0;\n"
                              "    b = 8'h3C;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x30u);
}

// ---------------------------------------------------------------------------
// 4. always_comb OR gate.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombOrGate) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, y;\n"
                              "  always_comb y = a | b;\n"
                              "  initial begin\n"
                              "    a = 8'hF0;\n"
                              "    b = 8'h0F;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

// ---------------------------------------------------------------------------
// 5. always_comb XOR gate.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombXorGate) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, y;\n"
                              "  always_comb y = a ^ b;\n"
                              "  initial begin\n"
                              "    a = 8'hAA;\n"
                              "    b = 8'h55;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

// ---------------------------------------------------------------------------
// 6. always_comb NOT (bitwise invert).
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombNotGate) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, y;\n"
                              "  always_comb y = ~a;\n"
                              "  initial begin\n"
                              "    a = 8'hA5;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // ~0xA5 = 0x5A in the low 8 bits; mask to declared width.
  EXPECT_EQ(y->value.ToUint64() & 0xFFu, 0x5Au);
}

// ---------------------------------------------------------------------------
// 7. always_comb if-else mux: select true branch.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombIfElseTrueBranch) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic sel;\n"
                              "  logic [7:0] a, b, y;\n"
                              "  always_comb\n"
                              "    if (sel) y = a;\n"
                              "    else y = b;\n"
                              "  initial begin\n"
                              "    a = 8'hAA;\n"
                              "    b = 8'hBB;\n"
                              "    sel = 1;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xAAu);
}

// ---------------------------------------------------------------------------
// 8. always_comb if-else mux: select false branch.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombIfElseFalseBranch) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic sel;\n"
                              "  logic [7:0] a, b, y;\n"
                              "  always_comb\n"
                              "    if (sel) y = a;\n"
                              "    else y = b;\n"
                              "  initial begin\n"
                              "    a = 8'hAA;\n"
                              "    b = 8'hBB;\n"
                              "    sel = 0;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xBBu);
}

// ---------------------------------------------------------------------------
// 9. always_comb case statement: matching branch.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombCaseMatch) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [1:0] sel;\n"
                              "  logic [7:0] y;\n"
                              "  always_comb\n"
                              "    case (sel)\n"
                              "      2'b00: y = 8'h10;\n"
                              "      2'b01: y = 8'h20;\n"
                              "      2'b10: y = 8'h30;\n"
                              "      default: y = 8'hFF;\n"
                              "    endcase\n"
                              "  initial begin\n"
                              "    sel = 2'b10;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x30u);
}

// ---------------------------------------------------------------------------
// 10. always_comb case statement: default branch.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombCaseDefault) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [1:0] sel;\n"
                              "  logic [7:0] y;\n"
                              "  always_comb\n"
                              "    case (sel)\n"
                              "      2'b00: y = 8'h10;\n"
                              "      2'b01: y = 8'h20;\n"
                              "      default: y = 8'hFF;\n"
                              "    endcase\n"
                              "  initial begin\n"
                              "    sel = 2'b11;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

// ---------------------------------------------------------------------------
// 11. Multiple always_comb blocks all evaluate at time 0.
// ---------------------------------------------------------------------------
TEST(SimCh9b, MultipleAlwaysCombTime0) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x, y;\n"
                              "  always_comb x = 8'h11;\n"
                              "  always_comb y = 8'h22;\n"
                              "  initial #1 $finish;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *x = f.ctx.FindVariable("x");
  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x11u);
  EXPECT_EQ(y->value.ToUint64(), 0x22u);
}

// ---------------------------------------------------------------------------
// 12. always_comb output available in initial block after scheduler run.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombOutputAfterRun) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [31:0] result;\n"
                              "  always_comb result = 100;\n"
                              "  initial #1 $finish;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 100u);
}

// ---------------------------------------------------------------------------
// 13. always_comb with function call.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombFunctionCall) {
  SimCh9bFixture f;
  auto *design =
      ElaborateSrc("module t;\n"
                   "  function logic [7:0] double_val(input logic [7:0] x);\n"
                   "    return x * 2;\n"
                   "  endfunction\n"
                   "  logic [7:0] a, y;\n"
                   "  always_comb y = double_val(a);\n"
                   "  initial begin\n"
                   "    a = 8'h15;\n"
                   "    #1 $finish;\n"
                   "  end\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // 0x15 * 2 = 0x2A.
  EXPECT_EQ(y->value.ToUint64(), 0x2Au);
}

// ---------------------------------------------------------------------------
// 14. always_comb with concatenation.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombConcatenation) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [3:0] hi, lo;\n"
                              "  logic [7:0] y;\n"
                              "  always_comb y = {hi, lo};\n"
                              "  initial begin\n"
                              "    hi = 4'hA;\n"
                              "    lo = 4'h5;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xA5u);
}

// ---------------------------------------------------------------------------
// 15. always_comb with ternary operator: false condition.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombTernaryFalse) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic sel;\n"
                              "  logic [7:0] a, b, y;\n"
                              "  always_comb y = sel ? a : b;\n"
                              "  initial begin\n"
                              "    a = 8'hCA;\n"
                              "    b = 8'hFE;\n"
                              "    sel = 0;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFEu);
}

// ---------------------------------------------------------------------------
// 16. always_comb with ternary operator: true condition.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombTernaryTrue) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic sel;\n"
                              "  logic [7:0] a, b, y;\n"
                              "  always_comb y = sel ? a : b;\n"
                              "  initial begin\n"
                              "    a = 8'hCA;\n"
                              "    b = 8'hFE;\n"
                              "    sel = 1;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xCAu);
}

// ---------------------------------------------------------------------------
// 17. always_comb with reduction AND.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombReductionAnd) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a;\n"
                              "  logic y;\n"
                              "  always_comb y = &a;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // &8'hFF = 1 (all bits set).
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 18. always_comb with reduction OR.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombReductionOr) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a;\n"
                              "  logic y;\n"
                              "  always_comb y = |a;\n"
                              "  initial begin\n"
                              "    a = 8'h01;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // |8'h01 = 1 (at least one bit set).
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 19. always_comb re-triggers when input changes.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombRetriggersOnChange) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [31:0] a, y;\n"
                              "  always_comb y = a + 1;\n"
                              "  initial begin\n"
                              "    a = 10;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 11u);
}

// ---------------------------------------------------------------------------
// 20. always_comb with multi-bit addition (16-bit).
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombMultiBitAdd) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [15:0] a, b, y;\n"
                              "  always_comb y = a + b;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x5555u);
}

// ---------------------------------------------------------------------------
// 21. always_comb with begin-end block and multiple outputs.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombBlockMultipleOutputs) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, sum, diff;\n"
                              "  always_comb begin\n"
                              "    sum = a + b;\n"
                              "    diff = a - b;\n"
                              "  end\n"
                              "  initial begin\n"
                              "    a = 8'h20;\n"
                              "    b = 8'h05;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *sum = f.ctx.FindVariable("sum");
  auto *diff = f.ctx.FindVariable("diff");
  ASSERT_NE(sum, nullptr);
  ASSERT_NE(diff, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 0x25u);
  EXPECT_EQ(diff->value.ToUint64(), 0x1Bu);
}

// ---------------------------------------------------------------------------
// 22. always_comb with left shift.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombLeftShift) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] data, y;\n"
                              "  always_comb y = data << 2;\n"
                              "  initial begin\n"
                              "    data = 8'h0F;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // 0x0F << 2 = 0x3C.
  EXPECT_EQ(y->value.ToUint64(), 0x3Cu);
}

// ---------------------------------------------------------------------------
// 23. always_comb with right shift.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombRightShift) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] data, y;\n"
                              "  always_comb y = data >> 4;\n"
                              "  initial begin\n"
                              "    data = 8'hF0;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // 0xF0 >> 4 = 0x0F.
  EXPECT_EQ(y->value.ToUint64(), 0x0Fu);
}

// ---------------------------------------------------------------------------
// 24. always_comb with comparison operator (greater-than).
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombComparison) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, y;\n"
                              "  always_comb\n"
                              "    if (a > b) y = a;\n"
                              "    else y = b;\n"
                              "  initial begin\n"
                              "    a = 8'h50;\n"
                              "    b = 8'h30;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // a > b is true, so y = a = 0x50.
  EXPECT_EQ(y->value.ToUint64(), 0x50u);
}

// ---------------------------------------------------------------------------
// 25. always_comb with equality comparison.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombEqualityCheck) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b;\n"
                              "  logic y;\n"
                              "  always_comb y = (a == b);\n"
                              "  initial begin\n"
                              "    a = 8'h42;\n"
                              "    b = 8'h42;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // a == b is true -> y = 1.
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 26. always_comb sensitivity: changes signal 'a', observes result.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombSensitivityRegistered) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [31:0] a, b;\n"
                              "  always_comb b = a + 1;\n"
                              "  initial #1 $finish;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  // Sensitivity map should have signal 'a' mapped.
  const auto &procs = f.ctx.GetSensitiveProcesses("a");
  EXPECT_FALSE(procs.empty());
}

// ---------------------------------------------------------------------------
// 27. always_comb with subtraction.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombSubtraction) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, y;\n"
                              "  always_comb y = a - b;\n"
                              "  initial begin\n"
                              "    a = 8'h50;\n"
                              "    b = 8'h10;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x40u);
}

// ---------------------------------------------------------------------------
// 28. always_comb with multiplication.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombMultiplication) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [15:0] a, b, y;\n"
                              "  always_comb y = a * b;\n"
                              "  initial begin\n"
                              "    a = 16'd7;\n"
                              "    b = 16'd6;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 42u);
}

// ---------------------------------------------------------------------------
// 29. always_comb with NAND expression (~(a & b)), masked to width.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombNand) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, y;\n"
                              "  always_comb y = ~(a & b);\n"
                              "  initial begin\n"
                              "    a = 8'hFF;\n"
                              "    b = 8'h0F;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // ~(0xFF & 0x0F) = ~0x0F = 0xF0 in the low 8 bits.
  EXPECT_EQ(y->value.ToUint64() & 0xFFu, 0xF0u);
}

// ---------------------------------------------------------------------------
// 30. always_comb with chained combinational logic: a XOR b, then OR c.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombChainedLogic) {
  SimCh9bFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, c, y;\n"
                              "  always_comb y = (a ^ b) | c;\n"
                              "  initial begin\n"
                              "    a = 8'hA0;\n"
                              "    b = 8'h50;\n"
                              "    c = 8'h0F;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // (0xA0 ^ 0x50) | 0x0F = 0xF0 | 0x0F = 0xFF.
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}
