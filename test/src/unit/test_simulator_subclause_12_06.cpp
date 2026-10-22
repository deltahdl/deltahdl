

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_lower_run.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(Matches, ExactMatchTrue) {
  SimFixture f;
  auto* expr = ParseExprFrom("42 matches 42", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kBinary);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Matches, ExactMatchFalse) {
  SimFixture f;
  auto* expr = ParseExprFrom("42 matches 99", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, VariableMatch) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("sig", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);
  auto* expr = ParseExprFrom("sig matches 8'hAB", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §12.6: a constant expression pattern (11.2.1) succeeds when the value equals
// its value. The constant here is a localparam, not a literal, so it exercises
// the parameter-resolution code path end-to-end (elaborate + lower + run).
TEST(Matches, ConstantLocalparamPatternMatchesRuntime) {
  SimFixture f;
  uint64_t y = RunModule(f,
                         "module t;\n"
                         "  localparam int P = 5;\n"
                         "  logic [7:0] x;\n"
                         "  logic y;\n"
                         "  initial begin\n"
                         "    x = 8'd5;\n"
                         "    y = x matches P;\n"
                         "  end\n"
                         "endmodule\n",
                         "y");
  EXPECT_EQ(y, 1u);
  EXPECT_FALSE(f.has_errors);
}

// §12.6: same constant expression pattern rule, but the constant is a module
// parameter and the value differs from it, so the match fails (result 0).
TEST(Matches, ConstantParameterPatternNoMatchRuntime) {
  SimFixture f;
  uint64_t y = RunModule(f,
                         "module t #(parameter int Q = 6);\n"
                         "  logic [7:0] x;\n"
                         "  logic y;\n"
                         "  initial begin\n"
                         "    x = 8'd3;\n"
                         "    y = x matches Q;\n"
                         "  end\n"
                         "endmodule\n",
                         "y");
  EXPECT_EQ(y, 0u);
  EXPECT_FALSE(f.has_errors);
}

// §12.6 (printed page 325): a constant expression pattern succeeds when the
// value equals the constant's value; §12.6.2 (printed 328) matches `e matches
// p` the same way. A 96-bit value equal to a 96-bit constant in every word
// matches, and one that differs from it only at bit 80 -- in the second 64-bit
// word -- does not. The two results are read together as eq * 10 + ne.
TEST(Matches, ConstantPatternWiderThanOneWordComparesEveryWord) {
  SimFixture f;
  uint64_t r = RunModule(
      f,
      "module t;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  logic [95:0] x;\n"
      "  int eq, ne, r;\n"
      "  initial begin\n"
      "    x = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    eq = x matches P;\n"
      "    x = 96'h0122_4567_89AB_CDEF_0011_2233;\n"
      "    ne = x matches P;\n"
      "    r = eq * 10 + ne;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(r, 10u);
  EXPECT_FALSE(f.has_errors);
}

// §12.6 (printed page 325): the same rule with a 32-bit constant against a
// 96-bit value, the constant extended to the value's width. The value whose
// low word alone holds the constant and whose bit 64 is set differs from it;
// the value holding the constant with clear upper words equals it. The two
// results are read together as high_set * 10 + high_clear.
TEST(Matches, ConstantPatternNarrowerThanTheValueExtendsToItsWidth) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  localparam logic [31:0] P = 32'h0011_2233;\n"
                         "  logic [95:0] x;\n"
                         "  int high_set, high_clear, r;\n"
                         "  initial begin\n"
                         "    x = 96'h1_0000_0000_0011_2233;\n"
                         "    high_set = x matches P;\n"
                         "    x = 96'h0011_2233;\n"
                         "    high_clear = x matches P;\n"
                         "    r = high_set * 10 + high_clear;\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 1u);
  EXPECT_FALSE(f.has_errors);
}

// §12.6.1 lets pattern matching ignore bits only in casez (z) and casex (x
// and z); a `matches` clause compares every bit, so an x or a z in the
// constant pattern matches only an x or a z in the value, never a 0 or a 1.
TEST(Matches, XInPatternIsNoWildcard) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("wv", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* expr = ParseExprFrom("wv matches 4'b1x1x", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, ZInPatternIsNoWildcard) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("zv", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* expr = ParseExprFrom("zv matches 4'b1?0?", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, WildcardPatternMismatch) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("mm", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b0010);

  auto* expr = ParseExprFrom("mm matches 4'b1x1x", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, ResultAlwaysDetermined) {
  SimFixture f;
  MakeVar4(f, "xv", 4, 0b0000, 0b1111);
  auto* expr = ParseExprFrom("xv matches 4'b0000", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.width, 1u);
}

// §12.6: even when the pattern contains x or z bits, the 1-bit result must be
// 0 or 1 — never x or z.
TEST(Matches, ResultDeterminedWhenPatternHasXZ) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("pv", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* expr = ParseExprFrom("pv matches 4'b1x1z", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.width, 1u);
}

// §12.6: result is 1-bit even when both the value and the pattern carry x/z.
TEST(Matches, ResultDeterminedWhenValueAndPatternHaveXZ) {
  SimFixture f;
  MakeVar4(f, "vp", 4, 0b1010, 0b0101);
  auto* expr = ParseExprFrom("vp matches 4'b1x1z", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.width, 1u);
}

// §12.6: the 1-bit result is 0 (fail) — never x or z — even when the value
// being matched carries x/z bits and the pattern cannot match it.
TEST(Matches, ResultDeterminedFalseWithValueXZ) {
  SimFixture f;
  // aval 0b1010 with bval 0b0101 makes two of the value's bits x/z.
  MakeVar4(f, "fv", 4, 0b1010, 0b0101);
  auto* expr = ParseExprFrom("fv matches 4'b0101", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, TripleAmpTrue) {
  SimFixture f;
  auto* expr = ParseExprFrom("1 &&& 1", f);
  ASSERT_NE(expr, nullptr);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Matches, TripleAmpFalseShortCircuit) {
  SimFixture f;
  auto* expr = ParseExprFrom("0 &&& 1", f);
  ASSERT_NE(expr, nullptr);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, TripleAmpSecondFalse) {
  SimFixture f;
  auto* expr = ParseExprFrom("1 &&& 0", f);
  ASSERT_NE(expr, nullptr);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §12.6 gives a pattern identifier the type of the part of the value it
// matches, so `.s` bound to the anonymous structure member `Add` is that
// structure, and §7.2 selects its members by name: s.reg1 and s.regd read the
// 1 and 6 the value holds, in a process and in a function body alike. The
// binding carried the member's bits without its layout, and each select read 0.
TEST(PatternMatchSim, IdentifierBoundToStructureMemberSelectsItsMembers) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module t;\n"
                "  typedef union tagged {\n"
                "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
                "    bit [9:0] JmpU;\n"
                "  } Instr;\n"
                "  Instr instr;\n"
                "  function automatic void f(Instr x);\n"
                "    case (x) matches\n"
                "      tagged Add .s : $display(\"%0d %0d\", s.reg1, s.regd);\n"
                "    endcase\n"
                "  endfunction\n"
                "  initial begin\n"
                "    instr = tagged Add '{1, 2, 6};\n"
                "    case (instr) matches\n"
                "      tagged Add .s : $display(\"%0d %0d\", s.reg1, s.regd);\n"
                "    endcase\n"
                "    f(instr);\n"
                "  end\n"
                "endmodule\n",
                f),
            "1 6\n1 6\n");
}

// Syntax 12-4 ends `tagged Valid .*` before the `&&&` filter, so the false
// flag fails the predicate and x is 2 (§12.6.2), and `tagged Invalid` ends
// before `?`, so the conditional on the failed match adds 20 (§12.6.3).
TEST(PatternMatchingSim, TaggedMemberPatternStopsAtFilterAndQuestion) {
  SimFixture f;
  // deltahdl reports the wildcard pattern .* as an unresolved identifier
  // (#7614); the excuse goes with the fix.
  f.has_errors.Excuse();
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
                 "  VInt v = tagged Valid 3;\n"
                 "  logic flag = 0;\n"
                 "  int x;\n"
                 "  initial begin\n"
                 "    if (v matches tagged Valid .* &&& flag) x = 1;\n"
                 "    else x = 2;\n"
                 "    x += v matches tagged Invalid ? 10 : 20;\n"
                 "    $display(\"%0d\", x);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "22\n");
}

// §12.6 declares a pattern identifier as a variable of the member's type,
// here a 2-state vector's and an enumeration's, each read as the member
// holds it. A real member's is #6418's to show, its union storing the real
// converted to an integer.
TEST(PatternMatchingSim, BoundVariableHasTheMembersType) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef enum {A, B, C} E;\n"
      "  typedef union tagged { bit [3:0] Bt; int I; } U2;\n"
      "  typedef union tagged { E En; int I; } U3;\n"
      "  U2 u2 = tagged Bt 4'd3;\n"
      "  U3 u3 = tagged En B;\n"
      "  int r = 0;\n"
      "  initial begin\n"
      "    if (u2 matches tagged Bt .b) r += b * 100;\n"
      "    if (u3 matches tagged En .ev) if (ev == B) r += 1000;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 1300u);
}

// §12.6 binds a pattern identifier to the member's value with the member's
// type, so one bound to a real member is the real it holds (#6418).
TEST(PatternMatchingSim, BoundRealMemberIsReal) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { real R; int I; } U;\n"
      "  U u;\n"
      "  int r = 0;\n"
      "  initial begin\n"
      "    u = tagged R 2.5;\n"
      "    if (u matches tagged R .x) r = int'(x * 4);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 10u);
}

// §12.6 matches the subject's value once, so an element subject's index is
// evaluated once: `arr[i++]` advances i once, and the value and the tag it is
// matched against are both arr[0]'s (#6421).
TEST(PatternMatchingSim, ElementSubjectIndexEvaluatedOnce) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt arr [4];\n"
      "  int i = 0;\n"
      "  int n = 0;\n"
      "  initial begin\n"
      "    arr[0] = tagged Valid 3;\n"
      "    arr[1] = tagged Valid 5;\n"
      "    if (arr[i++] matches tagged Valid .v) n = v;\n"
      "    n = n * 10 + i;\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 31u);
}

// §12.6 gives a pattern identifier the type of the member it binds, and a
// class handle member binds a handle of that class, through which §8.4
// reaches the class's methods (#6412).
TEST(PatternMatchingSim, ClassHandleMemberBindsAHandle) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    int v = 3;\n"
      "    function int get(); return v; endfunction\n"
      "  endclass\n"
      "  typedef union tagged { C h; int i; } U;\n"
      "  U u;\n"
      "  int r = 0;\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    u = tagged h c;\n"
      "    if (u matches tagged h .x) r = x.get() * 10 + x.v;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 33u);
}

}  // namespace
