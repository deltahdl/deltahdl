#include <gtest/gtest.h>

#include <string>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "lexer/token.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(OperatorSim, BinaryWildcardEq) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 ==? 8'd5);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryWildcardNeq) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 !=? 8'd3);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EvalOp, WildcardEqMismatch) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, WildcardNeqSame) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(OperatorSim, WildcardNeqLhsXNotUnderWildcardYieldsXAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b01x1;\n"
      "    b = 4'b0101;\n"
      "    r = (a !=? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_NE(r->value.words[0].bval & 1u, 0u);
}

TEST(OperatorSim, WildcardNeqRhsWildcardMatchYieldsZeroAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b0111;\n"
      "    b = 4'b01x1;\n"
      "    r = (a !=? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 0u);
}

TEST(EvalOp, WildcardEqResultIsOneBit) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, WildcardNeqResultIsOneBit) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(OperatorSim, WildcardEqWithXLiteral) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic r;\n"
      "  initial r = (4'b0101 ==? 4'b01x1);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, WildcardEqUnequalWidthExtendsNarrowOperand) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [3:0] narrow;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    wide = 8'b00010101;\n"
      "    narrow = 4'b0101;\n"
      "    r = (wide ==? narrow);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 0u);
}

TEST(OperatorSim, WildcardEqUnequalWidthMatchesAfterExtension) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [3:0] narrow;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    wide = 8'b00000101;\n"
      "    narrow = 4'b0101;\n"
      "    r = (wide ==? narrow);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

TEST(OperatorSim, WildcardNeqUnequalWidthExtendsNarrowOperand) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [3:0] narrow;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    wide = 8'b00010101;\n"
      "    narrow = 4'b0101;\n"
      "    r = (wide !=? narrow);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

TEST(OperatorSim, WildcardNeqWithXLiteral) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic r;\n"
      "  initial r = (4'b1101 !=? 4'b01x1);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, WildcardEqLhsXNotUnderWildcardYieldsXAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b01x1;\n"
      "    b = 4'b0101;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_NE(r->value.words[0].bval & 1u, 0u);
}

TEST(OperatorSim, WildcardEqLhsXUnderRhsWildcardIsKnownAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b01x1;\n"
      "    b = 4'b01x1;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

TEST(OperatorSim, WildcardEqNonWildcardMismatchYieldsZeroAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1101;\n"
      "    b = 4'b01x1;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 0u);
}

TEST(OperatorSim, WildcardEqClassHandlesEqualAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C; endclass\n"
      "module t;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    C h1;\n"
      "    C h2;\n"
      "    h1 = new;\n"
      "    h2 = h1;\n"
      "    r = (h1 ==? h2);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, WildcardEqClassHandlesUnequalAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C; endclass\n"
      "module t;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    C h1;\n"
      "    C h2;\n"
      "    h1 = new;\n"
      "    h2 = new;\n"
      "    r = (h1 ==? h2);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(OperatorSim, WildcardEqClassHandleWithNullAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C; endclass\n"
      "module t;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    C h;\n"
      "    h = new;\n"
      "    r = (h ==? null);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(OperatorSim, WildcardNeqClassHandleWithNullAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C; endclass\n"
      "module t;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    C h;\n"
      "    h = new;\n"
      "    r = (h !=? null);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, WildcardEqRhsZActsAsWildcardAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b0111;\n"
      "    b = 4'b01z1;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

TEST(OperatorSim, WildcardEqLhsZNotUnderWildcardYieldsXAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b01z1;\n"
      "    b = 4'b0101;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_NE(r->value.words[0].bval & 1u, 0u);
}

TEST(OperatorSim, WildcardEqChandleEquivalenceAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  chandle c;\n"
      "  logic r;\n"
      "  initial r = (c ==? null);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

TEST(OperatorSim, WildcardNeqChandleEquivalenceAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  chandle c;\n"
      "  logic r;\n"
      "  initial r = (c !=? null);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0u);
}

TEST(OperatorSim, WildcardEqInterfaceClassHandleEquivalenceAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "interface class IC;\n"
      "  pure virtual function int get();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function int get(); return 1; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    IC a;\n"
      "    IC b;\n"
      "    C c;\n"
      "    c = new;\n"
      "    a = c;\n"
      "    b = c;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

TEST(OperatorSim, WildcardEqWiderThanOneWordComparesEveryWord) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [95:0] a, b;\n"
      "  int eq, ne, r;\n"
      "  initial begin\n"
      "    a = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    b = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    eq = (a ==? b);\n"
      "    a = 96'h0122_4567_89AB_CDEF_0011_2233;\n"
      "    ne = (a ==? b);\n"
      "    r = eq * 10 + ne;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 10u);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorSim, WildcardEqRhsWildcardAboveBit63MasksItsOwnBitAlone) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [95:0] a, b;\n"
      "  int under, outside, r;\n"
      "  initial begin\n"
      "    b = 96'h012x_4567_89AB_CDEF_0011_2233;\n"
      "    a = 96'h0129_4567_89AB_CDEF_0011_2233;\n"
      "    under = (a ==? b);\n"
      "    a = 96'h0523_4567_89AB_CDEF_0011_2233;\n"
      "    outside = (a ==? b);\n"
      "    r = under * 10 + outside;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 10u);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorSim, WildcardEqLhsXAboveBit63NotUnderWildcardYieldsX) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [95:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 96'h012x_4567_89AB_CDEF_0011_2233;\n"
      "    b = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_NE(r->value.words[0].bval & 1u, 0u);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorSim, WildcardNeqWiderThanOneWordComparesEveryWord) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [95:0] a, b;\n"
      "  int ne, eq, wild, r;\n"
      "  initial begin\n"
      "    b = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    a = 96'h0122_4567_89AB_CDEF_0011_2233;\n"
      "    ne = (a !=? b);\n"
      "    a = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    eq = (a !=? b);\n"
      "    b = 96'h012x_4567_89AB_CDEF_0011_2233;\n"
      "    a = 96'h0129_4567_89AB_CDEF_0011_2233;\n"
      "    wild = (a !=? b);\n"
      "    r = ne * 100 + eq * 10 + wild;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 100u);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorSim, LogicalEqWiderThanOneWordComparesEveryWord) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [95:0] a, b;\n"
      "  int eq_same, eq_diff, ne_diff, r;\n"
      "  initial begin\n"
      "    a = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    b = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    eq_same = (a == b);\n"
      "    a = 96'h0122_4567_89AB_CDEF_0011_2233;\n"
      "    eq_diff = (a == b);\n"
      "    ne_diff = (a != b);\n"
      "    r = eq_same * 100 + eq_diff * 10 + ne_diff;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 101u);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorSim, WildcardEqKnownMismatchDecidesDespiteLhsX) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [3:0] a = 4'b1x00;\n"
                       "  initial $display(\"%b %b %b %b\", a == 4'b0000,\n"
                       "      a ==? 4'b0000, a !=? 4'b0000, a ==? 4'b1000);\n"
                       "endmodule\n",
                       f),
            "0 0 1 x\n");
}

}  // namespace
