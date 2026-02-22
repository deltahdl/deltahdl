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

struct SimCh10Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimCh10Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// ---------------------------------------------------------------------------
// 1. Simple blocking assignment: a = 5; check a == 5.
// ---------------------------------------------------------------------------
TEST(SimCh10, SimpleBlockingAssign) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int a;\n"
                              "  initial begin\n"
                              "    a = 5;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// ---------------------------------------------------------------------------
// 2. Sequential blocking assignments: value available immediately.
// ---------------------------------------------------------------------------
TEST(SimCh10, SequentialBlockingImmediate) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int a, b;\n"
                              "  initial begin\n"
                              "    a = 1;\n"
                              "    b = a + 1;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 2u);
}

// ---------------------------------------------------------------------------
// 3. Blocking assignment with arithmetic expression.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignExpression) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int a;\n"
                              "  initial begin\n"
                              "    a = 3 * 4 + 1;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

// ---------------------------------------------------------------------------
// 4. Blocking assignment to bit-select.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignBitSelect) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a;\n"
                              "  initial begin\n"
                              "    a = 8'h00;\n"
                              "    a[0] = 1;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x01u);
}

// ---------------------------------------------------------------------------
// 5. Blocking assignment to part-select.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignPartSelect) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a;\n"
                              "  initial begin\n"
                              "    a = 8'h00;\n"
                              "    a[3:0] = 4'hF;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

// ---------------------------------------------------------------------------
// 6. Blocking assignment splitting a packed value into parts.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignSplitPacked) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [15:0] packed_val;\n"
                              "  logic [7:0] hi, lo;\n"
                              "  initial begin\n"
                              "    packed_val = 16'hDEAD;\n"
                              "    hi = packed_val[15:8];\n"
                              "    lo = packed_val[7:0];\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *hi = f.ctx.FindVariable("hi");
  auto *lo = f.ctx.FindVariable("lo");
  ASSERT_NE(hi, nullptr);
  ASSERT_NE(lo, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0xDEu);
  EXPECT_EQ(lo->value.ToUint64(), 0xADu);
}

// ---------------------------------------------------------------------------
// 7. Blocking assignment with concatenation on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignConcatRHS) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b;\n"
                              "  logic [15:0] c;\n"
                              "  initial begin\n"
                              "    a = 8'hCA;\n"
                              "    b = 8'hFE;\n"
                              "    c = {a, b};\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 0xCAFEu);
}

// ---------------------------------------------------------------------------
// 8. Blocking assignment with ternary on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignTernary) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int sel, result;\n"
                              "  initial begin\n"
                              "    sel = 1;\n"
                              "    result = sel ? 42 : 99;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// ---------------------------------------------------------------------------
// 9. Blocking assignment in if-else: sequential execution order matters.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignIfElse) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int x, y;\n"
                              "  initial begin\n"
                              "    x = 10;\n"
                              "    if (x == 10)\n"
                              "      y = 1;\n"
                              "    else\n"
                              "      y = 0;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 10. Blocking assignment in case statement.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignCase) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [1:0] sel;\n"
                              "  int result;\n"
                              "  initial begin\n"
                              "    sel = 2;\n"
                              "    case (sel)\n"
                              "      0: result = 10;\n"
                              "      1: result = 20;\n"
                              "      2: result = 30;\n"
                              "      default: result = 0;\n"
                              "    endcase\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

// ---------------------------------------------------------------------------
// 11. Blocking assignment in for loop (accumulate).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignForLoop) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int sum;\n"
                              "  int i;\n"
                              "  initial begin\n"
                              "    sum = 0;\n"
                              "    for (i = 1; i <= 5; i = i + 1) begin\n"
                              "      sum = sum + i;\n"
                              "    end\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("sum");
  ASSERT_NE(var, nullptr);
  // 1+2+3+4+5 = 15
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

// ---------------------------------------------------------------------------
// 12. Blocking assignment in begin-end block.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignBeginEnd) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int a, b, c;\n"
                              "  initial begin\n"
                              "    begin\n"
                              "      a = 10;\n"
                              "      b = 20;\n"
                              "      c = a + b;\n"
                              "    end\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 30u);
}

// ---------------------------------------------------------------------------
// 13. Blocking assignment with function call on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignFunctionCall) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  function integer add(integer a, integer b);\n"
                              "    return a + b;\n"
                              "  endfunction\n"
                              "  int result;\n"
                              "  initial begin\n"
                              "    result = add(7, 3);\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// ---------------------------------------------------------------------------
// 14. Blocking assignment with system function ($clog2) on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignSysClog2) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int result;\n"
                              "  initial begin\n"
                              "    result = $clog2(256);\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // $clog2(256) = 8
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

// ---------------------------------------------------------------------------
// 15. Blocking assignment with unary operators (~, !).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignUnaryOps) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int a;\n"
                              "  int r_not, r_bang;\n"
                              "  initial begin\n"
                              "    a = 0;\n"
                              "    r_not = !a;\n"
                              "    r_bang = !5;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *r_not = f.ctx.FindVariable("r_not");
  auto *r_bang = f.ctx.FindVariable("r_bang");
  ASSERT_NE(r_not, nullptr);
  ASSERT_NE(r_bang, nullptr);
  // !0 = 1
  EXPECT_EQ(r_not->value.ToUint64(), 1u);
  // !5 = 0
  EXPECT_EQ(r_bang->value.ToUint64(), 0u);
}

// ---------------------------------------------------------------------------
// 16. Blocking assignment with unary logical NOT (!) and unary minus (-).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignUnaryLogicalNotAndMinus) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int a, neg_result, not_result;\n"
                              "  initial begin\n"
                              "    a = 5;\n"
                              "    neg_result = -a;\n"
                              "    not_result = !a;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *neg = f.ctx.FindVariable("neg_result");
  ASSERT_NE(neg, nullptr);
  // -5 as 32-bit unsigned = 0xFFFFFFFB
  auto neg5_32bit = static_cast<uint32_t>(-5);
  EXPECT_EQ(neg->value.ToUint64(), neg5_32bit);

  auto *notv = f.ctx.FindVariable("not_result");
  ASSERT_NE(notv, nullptr);
  // !5 = 0
  EXPECT_EQ(notv->value.ToUint64(), 0u);
}

// ---------------------------------------------------------------------------
// 17. Blocking assignment with arithmetic operators (+, -, *, /).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignArithmeticOps) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int r_add, r_sub, r_mul, r_div;\n"
                              "  initial begin\n"
                              "    r_add = 10 + 3;\n"
                              "    r_sub = 10 - 3;\n"
                              "    r_mul = 10 * 3;\n"
                              "    r_div = 10 / 3;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *r_add = f.ctx.FindVariable("r_add");
  auto *r_sub = f.ctx.FindVariable("r_sub");
  auto *r_mul = f.ctx.FindVariable("r_mul");
  auto *r_div = f.ctx.FindVariable("r_div");
  ASSERT_NE(r_add, nullptr);
  ASSERT_NE(r_sub, nullptr);
  ASSERT_NE(r_mul, nullptr);
  ASSERT_NE(r_div, nullptr);
  EXPECT_EQ(r_add->value.ToUint64(), 13u);
  EXPECT_EQ(r_sub->value.ToUint64(), 7u);
  EXPECT_EQ(r_mul->value.ToUint64(), 30u);
  EXPECT_EQ(r_div->value.ToUint64(), 3u);
}

// ---------------------------------------------------------------------------
// 18. Blocking assignment with bitwise operators (&, |, ^).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignBitwiseOps) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int a, b;\n"
                              "  int r_and, r_or, r_xor;\n"
                              "  initial begin\n"
                              "    a = 240;\n"
                              "    b = 60;\n"
                              "    r_and = a & b;\n"
                              "    r_or  = a | b;\n"
                              "    r_xor = a ^ b;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *r_and = f.ctx.FindVariable("r_and");
  auto *r_or = f.ctx.FindVariable("r_or");
  auto *r_xor = f.ctx.FindVariable("r_xor");
  ASSERT_NE(r_and, nullptr);
  ASSERT_NE(r_or, nullptr);
  ASSERT_NE(r_xor, nullptr);
  // 240 & 60 = 48
  EXPECT_EQ(r_and->value.ToUint64(), 48u);
  // 240 | 60 = 252
  EXPECT_EQ(r_or->value.ToUint64(), 252u);
  // 240 ^ 60 = 204
  EXPECT_EQ(r_xor->value.ToUint64(), 204u);
}

// ---------------------------------------------------------------------------
// 19. Blocking assignment with shift operators (<<, >>).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignShiftOps) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a;\n"
                              "  logic [7:0] r_shl, r_shr;\n"
                              "  initial begin\n"
                              "    a = 8'h0F;\n"
                              "    r_shl = a << 2;\n"
                              "    r_shr = a >> 2;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *shl = f.ctx.FindVariable("r_shl");
  auto *shr = f.ctx.FindVariable("r_shr");
  ASSERT_NE(shl, nullptr);
  ASSERT_NE(shr, nullptr);
  // 0x0F << 2 = 0x3C (8-bit)
  EXPECT_EQ(shl->value.ToUint64(), 0x3Cu);
  // 0x0F >> 2 = 0x03
  EXPECT_EQ(shr->value.ToUint64(), 0x03u);
}

// ---------------------------------------------------------------------------
// 20. Blocking assignment with comparison operators.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignComparisonOps) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int a, b;\n"
                              "  int r_eq, r_ne, r_lt, r_gt, r_le, r_ge;\n"
                              "  initial begin\n"
                              "    a = 10;\n"
                              "    b = 20;\n"
                              "    r_eq = (a == b);\n"
                              "    r_ne = (a != b);\n"
                              "    r_lt = (a < b);\n"
                              "    r_gt = (a > b);\n"
                              "    r_le = (a <= b);\n"
                              "    r_ge = (a >= b);\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *r_eq = f.ctx.FindVariable("r_eq");
  auto *r_ne = f.ctx.FindVariable("r_ne");
  auto *r_lt = f.ctx.FindVariable("r_lt");
  auto *r_gt = f.ctx.FindVariable("r_gt");
  auto *r_le = f.ctx.FindVariable("r_le");
  auto *r_ge = f.ctx.FindVariable("r_ge");
  ASSERT_NE(r_eq, nullptr);
  ASSERT_NE(r_ne, nullptr);
  ASSERT_NE(r_lt, nullptr);
  ASSERT_NE(r_gt, nullptr);
  ASSERT_NE(r_le, nullptr);
  ASSERT_NE(r_ge, nullptr);
  EXPECT_EQ(r_eq->value.ToUint64(), 0u); // 10 == 20 -> false
  EXPECT_EQ(r_ne->value.ToUint64(), 1u); // 10 != 20 -> true
  EXPECT_EQ(r_lt->value.ToUint64(), 1u); // 10 < 20  -> true
  EXPECT_EQ(r_gt->value.ToUint64(), 0u); // 10 > 20  -> false
  EXPECT_EQ(r_le->value.ToUint64(), 1u); // 10 <= 20 -> true
  EXPECT_EQ(r_ge->value.ToUint64(), 0u); // 10 >= 20 -> false
}

// ---------------------------------------------------------------------------
// 21. Blocking assignment with logical operators (&&, ||).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignLogicalOps) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int a, b;\n"
                              "  int r_and, r_or;\n"
                              "  initial begin\n"
                              "    a = 1;\n"
                              "    b = 0;\n"
                              "    r_and = a && b;\n"
                              "    r_or  = a || b;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *r_and = f.ctx.FindVariable("r_and");
  auto *r_or = f.ctx.FindVariable("r_or");
  ASSERT_NE(r_and, nullptr);
  ASSERT_NE(r_or, nullptr);
  EXPECT_EQ(r_and->value.ToUint64(), 0u); // 1 && 0 = 0
  EXPECT_EQ(r_or->value.ToUint64(), 1u);  // 1 || 0 = 1
}

// ---------------------------------------------------------------------------
// 22. Multiple blocking assignments to same variable (last wins).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignLastWins) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int x;\n"
                              "  initial begin\n"
                              "    x = 1;\n"
                              "    x = 2;\n"
                              "    x = 3;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// ---------------------------------------------------------------------------
// 23. Blocking assignment chain: a=1; b=a; c=b; check c==1.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignChain) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int a, b, c;\n"
                              "  initial begin\n"
                              "    a = 1;\n"
                              "    b = a;\n"
                              "    c = b;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *a = f.ctx.FindVariable("a");
  auto *b = f.ctx.FindVariable("b");
  auto *c = f.ctx.FindVariable("c");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 1u);
  EXPECT_EQ(b->value.ToUint64(), 1u);
  EXPECT_EQ(c->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 24. Blocking assignment with type cast (signed').
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignTypeCast) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  int result;\n"
                              "  initial begin\n"
                              "    x = 8'hFF;\n"
                              "    result = signed'(x);\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // 8'hFF sign-extended to 32 bits = 0xFFFFFFFF.
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

// ---------------------------------------------------------------------------
// 25. Blocking assignment preserving width/truncation.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignTruncation) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [3:0] narrow;\n"
                              "  initial begin\n"
                              "    narrow = 8'hFF;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("narrow");
  ASSERT_NE(var, nullptr);
  // 8'hFF truncated to 4 bits = 0xF.
  EXPECT_EQ(var->value.width, 4u);
  EXPECT_EQ(var->value.ToUint64(), 0xFu);
}

// ---------------------------------------------------------------------------
// 26. Verify .width and .ToUint64() for 8-bit variable.
// ---------------------------------------------------------------------------
TEST(SimCh10, VerifyWidthAndToUint64_8bit) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] val;\n"
                              "  initial begin\n"
                              "    val = 8'hAB;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("val");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// ---------------------------------------------------------------------------
// 27. Verify .width and .ToUint64() for 32-bit int.
// ---------------------------------------------------------------------------
TEST(SimCh10, VerifyWidthAndToUint64_32bit) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int val;\n"
                              "  initial begin\n"
                              "    val = 32'hDEADBEEF;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("val");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

// ---------------------------------------------------------------------------
// 28. Blocking assignment with ternary false branch.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignTernaryFalse) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int sel, result;\n"
                              "  initial begin\n"
                              "    sel = 0;\n"
                              "    result = sel ? 42 : 99;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// ---------------------------------------------------------------------------
// 29. Blocking assignment with modulo operator (%).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignModulo) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int result;\n"
                              "  initial begin\n"
                              "    result = 17 % 5;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // 17 % 5 = 2
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// ---------------------------------------------------------------------------
// 30. Blocking assignment with unary plus (+).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignUnaryPlus) {
  SimCh10Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  int a, result;\n"
                              "  initial begin\n"
                              "    a = 42;\n"
                              "    result = +a;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}
