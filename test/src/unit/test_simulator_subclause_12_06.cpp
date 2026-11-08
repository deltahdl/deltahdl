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

Expr* ParsePredicateFrom(const std::string& predicate, SimFixture& f) {
  return ParseExprFrom(predicate + " ? 1 : 0", f)->condition;
}

TEST(Matches, ExactMatchTrue) {
  SimFixture f;
  auto* expr = ParsePredicateFrom("42 matches 42", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kBinary);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Matches, ExactMatchFalse) {
  SimFixture f;
  auto* expr = ParsePredicateFrom("42 matches 99", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, VariableMatch) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("sig", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);
  auto* expr = ParsePredicateFrom("sig matches 8'hAB", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Matches, ConstantLocalparamPatternMatchesRuntime) {
  SimFixture f;
  uint64_t y = RunModule(f,
                         "module t;\n"
                         "  localparam int P = 5;\n"
                         "  logic [7:0] x;\n"
                         "  logic y;\n"
                         "  initial begin\n"
                         "    x = 8'd5;\n"
                         "    y = x matches P ? 1 : 0;\n"
                         "  end\n"
                         "endmodule\n",
                         "y");
  EXPECT_EQ(y, 1u);
  EXPECT_FALSE(f.has_errors);
}

TEST(Matches, ConstantParameterPatternNoMatchRuntime) {
  SimFixture f;
  uint64_t y = RunModule(f,
                         "module t #(parameter int Q = 6);\n"
                         "  logic [7:0] x;\n"
                         "  logic y;\n"
                         "  initial begin\n"
                         "    x = 8'd3;\n"
                         "    y = x matches Q ? 1 : 0;\n"
                         "  end\n"
                         "endmodule\n",
                         "y");
  EXPECT_EQ(y, 0u);
  EXPECT_FALSE(f.has_errors);
}

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
      "    eq = x matches P ? 1 : 0;\n"
      "    x = 96'h0122_4567_89AB_CDEF_0011_2233;\n"
      "    ne = x matches P ? 1 : 0;\n"
      "    r = eq * 10 + ne;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(r, 10u);
  EXPECT_FALSE(f.has_errors);
}

TEST(Matches, ConstantPatternNarrowerThanTheValueExtendsToItsWidth) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  localparam logic [31:0] P = 32'h0011_2233;\n"
                         "  logic [95:0] x;\n"
                         "  int high_set, high_clear, r;\n"
                         "  initial begin\n"
                         "    x = 96'h1_0000_0000_0011_2233;\n"
                         "    high_set = x matches P ? 1 : 0;\n"
                         "    x = 96'h0011_2233;\n"
                         "    high_clear = x matches P ? 1 : 0;\n"
                         "    r = high_set * 10 + high_clear;\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 1u);
  EXPECT_FALSE(f.has_errors);
}

TEST(Matches, XInPatternIsNoWildcard) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("wv", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* expr = ParsePredicateFrom("wv matches 4'b1x1x", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, ZInPatternIsNoWildcard) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("zv", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* expr = ParsePredicateFrom("zv matches 4'b1?0?", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, WildcardPatternMismatch) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("mm", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b0010);

  auto* expr = ParsePredicateFrom("mm matches 4'b1x1x", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, ResultAlwaysDetermined) {
  SimFixture f;
  MakeVar4(f, "xv", 4, 0b0000, 0b1111);
  auto* expr = ParsePredicateFrom("xv matches 4'b0000", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.width, 1u);
}

TEST(Matches, ResultDeterminedWhenPatternHasXZ) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("pv", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* expr = ParsePredicateFrom("pv matches 4'b1x1z", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.width, 1u);
}

TEST(Matches, ResultDeterminedWhenValueAndPatternHaveXZ) {
  SimFixture f;
  MakeVar4(f, "vp", 4, 0b1010, 0b0101);
  auto* expr = ParsePredicateFrom("vp matches 4'b1x1z", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.width, 1u);
}

TEST(Matches, ResultDeterminedFalseWithValueXZ) {
  SimFixture f;
  MakeVar4(f, "fv", 4, 0b1010, 0b0101);
  auto* expr = ParsePredicateFrom("fv matches 4'b0101", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, TripleAmpTrue) {
  SimFixture f;
  auto* expr = ParsePredicateFrom("1 &&& 1", f);
  ASSERT_NE(expr, nullptr);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Matches, TripleAmpFalseShortCircuit) {
  SimFixture f;
  auto* expr = ParsePredicateFrom("0 &&& 1", f);
  ASSERT_NE(expr, nullptr);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, TripleAmpSecondFalse) {
  SimFixture f;
  auto* expr = ParsePredicateFrom("1 &&& 0", f);
  ASSERT_NE(expr, nullptr);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

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

TEST(PatternMatchingSim, TaggedMemberPatternStopsAtFilterAndQuestion) {
  SimFixture f;
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
