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

struct SimCh11Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimCh11Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// §11.4.6: Basic ternary with true condition selects true branch.
TEST(SimCh11, TernaryBasicTrue) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = 1 ? 10 : 20;\n"
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

// §11.4.6: Basic ternary with false condition selects false branch.
TEST(SimCh11, TernaryBasicFalse) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = 0 ? 10 : 20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// §11.4.6: Ternary with a variable condition (nonzero is true).
TEST(SimCh11, TernaryVariableCondition) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int cond;\n"
      "  int result;\n"
      "  initial begin\n"
      "    cond = 5;\n"
      "    result = cond ? 42 : 99;\n"
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

// §11.4.6: Ternary with comparison condition implements max(a, b).
TEST(SimCh11, TernaryComparisonMax) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 30;\n"
      "    b = 50;\n"
      "    result = (a > b) ? a : b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 50u);
}

// §11.4.6: Ternary with equality condition.
TEST(SimCh11, TernaryEqualityCondition) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a, result;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    result = (a == 0) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.4.6: Nested ternary — right-to-left associativity: a ? b ? 1 : 2 : 3.
TEST(SimCh11, TernaryNested) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 0;\n"
      "    result = a ? b ? 1 : 2 : 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // a=1 → inner: b=0 → 2.
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §11.4.6: Chained ternary as priority encoder: sel==0 ? a : sel==1 ? b : c.
TEST(SimCh11, TernaryChainedPriorityEncoder) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int sel, a, b, c, result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    a = 10;\n"
      "    b = 20;\n"
      "    c = 30;\n"
      "    result = (sel == 0) ? a : (sel == 1) ? b : c;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// §11.4.6: Ternary in continuous assignment.
TEST(SimCh11, TernaryContinuousAssign) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b;\n"
      "  wire [7:0] y;\n"
      "  assign y = sel ? a : b;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    a = 8'd55;\n"
      "    b = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_EQ(net->resolved->value.ToUint64(), 55u);
}

// §11.4.6: Ternary in blocking assignment.
TEST(SimCh11, TernaryBlockingAssign) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int x, result;\n"
      "  initial begin\n"
      "    x = 3;\n"
      "    result = (x != 0) ? 100 : 200;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 100u);
}

// §11.4.6: Ternary in nonblocking assignment.
TEST(SimCh11, TernaryNonblockingAssign) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, result;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    result <= sel ? 8'd11 : 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // sel=0 → false branch → 22.
  EXPECT_EQ(var->value.ToUint64(), 22u);
}

// §11.4.6: Ternary with bitwise AND in condition.
TEST(SimCh11, TernaryBitwiseCondition) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h0F;\n"
      "    result = (a & b) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // 0xF0 & 0x0F = 0x00 → false → 0.
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §11.4.6: Ternary with logical OR in condition.
TEST(SimCh11, TernaryLogicalOrCondition) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 1;\n"
      "    result = (a || b) ? 7 : 8;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // (0 || 1) is true → 7.
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// §11.4.6: Ternary with concatenation as result.
TEST(SimCh11, TernaryConcatResult) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] hi, lo;\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    hi = 8'hAB;\n"
      "    lo = 8'hCD;\n"
      "    result = 1 ? {hi, lo} : 16'h0000;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

// §11.4.6: Ternary with function call in branches.
TEST(SimCh11, TernaryFunctionCallBranch) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  function int double_it(int x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    result = sel ? double_it(5) : double_it(3);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // sel=1 → double_it(5) = 10.
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// §11.4.6: Ternary with different-width operands (wider result).
TEST(SimCh11, TernaryDifferentWidthOperands) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [7:0] wide;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    narrow = 4'hF;\n"
      "    wide = 8'hAA;\n"
      "    result = 0 ? narrow : wide;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

// §11.4.6: Ternary with signed operands preserves signedness.
TEST(SimCh11, TernarySignedOperands) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = -5;\n"
      "    b = 10;\n"
      "    result = (a < 0) ? a : b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // -5 as 32-bit unsigned = 0xFFFFFFFB.
  auto neg5_u32 = static_cast<uint32_t>(-5);
  EXPECT_EQ(var->value.ToUint64(), neg5_u32);
}

// §11.4.6: Ternary selecting between constants.
TEST(SimCh11, TernarySelectConstants) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 1 ? 8'd100 : 8'd200;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 100u);
}

// §11.4.6: Ternary in always_comb block.
TEST(SimCh11, TernaryAlwaysComb) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    a = 8'd33;\n"
      "    b = 8'd44;\n"
      "  end\n"
      "  always_comb begin\n"
      "    y = sel ? a : b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

// §11.4.6: Ternary result used as function argument.
TEST(SimCh11, TernaryAsFunctionArgument) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  function int add_one(int x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    result = add_one(sel ? 10 : 20);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // sel=0 → 20, add_one(20) = 21.
  EXPECT_EQ(var->value.ToUint64(), 21u);
}

// §11.4.6: Ternary with arithmetic in branches: sel ? (a+b) : (a-b).
TEST(SimCh11, TernaryArithmeticBranches) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int sel, a, b, result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    a = 15;\n"
      "    b = 5;\n"
      "    result = sel ? (a + b) : (a - b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // sel=1 → a+b = 20.
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// §11.4.6: Ternary with unary NOT in condition: !sel ? a : b.
TEST(SimCh11, TernaryUnaryNotCondition) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    result = !sel ? 77 : 88;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // !0 = 1 → true branch → 77.
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

// §11.4.6: Multiple ternaries combined in one expression.
TEST(SimCh11, TernaryMultipleInExpression) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 0;\n"
      "    result = (a ? 10 : 20) + (b ? 30 : 40);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // (1?10:20) + (0?30:40) = 10 + 40 = 50.
  EXPECT_EQ(var->value.ToUint64(), 50u);
}

// §11.4.6: Ternary result used in further computation.
TEST(SimCh11, TernaryResultInComputation) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    result = (sel ? 6 : 3) * 7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // (1?6:3) * 7 = 6 * 7 = 42.
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §11.4.6: Ternary with bit-select condition.
TEST(SimCh11, TernaryBitSelectCondition) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] flags;\n"
      "  int result;\n"
      "  initial begin\n"
      "    flags = 8'b0000_0100;\n"
      "    result = flags[2] ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // flags[2] = 1 → true → 1.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.4.6: Ternary with part-select operands.
TEST(SimCh11, TernaryPartSelectOperands) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    data = 16'hABCD;\n"
      "    result = 1 ? data[15:8] : data[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // True branch: data[15:8] = 0xAB.
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// §11.4.6: Verify .width on ternary result with 8-bit operands.
TEST(SimCh11, TernaryResultWidth8Bit) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'h01;\n"
      "    result = 1 ? a : b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// §11.4.6: Verify .width and .ToUint64() on ternary result with 32-bit int.
TEST(SimCh11, TernaryResultWidth32Bit) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = 1 ? 32'hDEAD_BEEF : 32'h0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

// §11.4.6: Nested ternary — outer false, inner not reached.
TEST(SimCh11, TernaryNestedOuterFalse) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = 0 ? (1 ? 10 : 20) : 30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // Outer condition 0 → false branch → 30.
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

// §11.4.6: Chained ternary selects last default when no match.
TEST(SimCh11, TernaryChainedDefault) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 5;\n"
      "    result = (sel == 0) ? 100 :\n"
      "             (sel == 1) ? 200 :\n"
      "             (sel == 2) ? 300 : 999;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // No match → default 999.
  EXPECT_EQ(var->value.ToUint64(), 999u);
}

// §11.4.6: Ternary with logical AND in condition.
TEST(SimCh11, TernaryLogicalAndCondition) {
  SimCh11Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 3;\n"
      "    b = 4;\n"
      "    result = (a && b) ? 55 : 66;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // (3 && 4) is true → 55.
  EXPECT_EQ(var->value.ToUint64(), 55u);
}
