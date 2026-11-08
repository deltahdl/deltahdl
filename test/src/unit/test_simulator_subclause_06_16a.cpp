#include <gtest/gtest.h>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_string_var.h"
#include "lexer/token.h"
#include "simulator/adv_sim.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StringDataType, DefaultEmptyString) {
  SvString s;
  EXPECT_EQ(s.Len(), 0u);
  EXPECT_EQ(s.Get(), "");
}

TEST(StringDataType, StringSetAndGet) {
  SvString s;
  s.Set("hello");
  EXPECT_EQ(s.Get(), "hello");
  EXPECT_EQ(s.Len(), 5u);
}

TEST(StringDataType, StringEqualityComparison) {
  SvString a;
  SvString b;
  a.Set("abc");
  b.Set("abc");
  EXPECT_TRUE(a == b);
  b.Set("xyz");
  EXPECT_FALSE(a == b);
}

TEST(StringDataType, IdentifierStringPropagation) {
  SimFixture f;
  MakeStringVar(f, "sv2", "test");
  auto result = EvalExpr(MakeId(f.arena, "sv2"), f.ctx, f.arena);
  EXPECT_TRUE(result.is_string);
}

TEST(StringDataType, StringInequalityOp) {
  SimFixture f;
  MakeStringVar(f, "a", "abc");
  MakeStringVar(f, "b", "xyz");
  auto* ne = MakeBinary(f.arena, TokenKind::kBangEq, MakeId(f.arena, "a"),
                        MakeId(f.arena, "b"));
  auto result = EvalExpr(ne, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(StringDataType, StringEqualityOpSameValue) {
  SimFixture f;
  MakeStringVar(f, "a", "hello");
  MakeStringVar(f, "b", "hello");
  auto* eq = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "a"),
                        MakeId(f.arena, "b"));
  auto result = EvalExpr(eq, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(StringDataType, StringRelationalGreaterThan) {
  SimFixture f;
  MakeStringVar(f, "a", "xyz");
  MakeStringVar(f, "b", "abc");
  auto* gt = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "a"),
                        MakeId(f.arena, "b"));
  auto result = EvalExpr(gt, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(StringDataType, StringRelationalLessEqual) {
  SimFixture f;
  MakeStringVar(f, "a", "abc");
  MakeStringVar(f, "b", "abc");
  auto* le = MakeBinary(f.arena, TokenKind::kLtEq, MakeId(f.arena, "a"),
                        MakeId(f.arena, "b"));
  auto result = EvalExpr(le, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(StringDataType, StringRelationalGreaterEqual) {
  SimFixture f;
  MakeStringVar(f, "a", "def");
  MakeStringVar(f, "b", "abc");
  auto* ge = MakeBinary(f.arena, TokenKind::kGtEq, MakeId(f.arena, "a"),
                        MakeId(f.arena, "b"));
  auto result = EvalExpr(ge, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(StringDataType, StringAssignFromString) {
  SimFixture f;
  auto* var_b = RunAndFindVar(
      "module m;\n"
      "  string a, b;\n"
      "  initial begin\n"
      "    a = \"test\";\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var_b, nullptr);
  EXPECT_EQ(VecToStr(var_b->value), "test");
}

TEST(StringDataType, StringLiteralEmbeddedZeroStrippedInInit) {
  SimFixture f;
  auto* s1 = RunAndFindVar(
      "module m;\n"
      "  string s1 = \"hello\\0world\";\n"
      "endmodule\n",
      f, "s1");
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(VecToStr(s1->value), "helloworld");
}

TEST(StringDataType, StringLiteralEmbeddedZeroStrippedInProceduralAssign) {
  SimFixture f;
  auto* s = RunAndFindVar(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"foo\\0bar\";\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "foobar");
}

TEST(StringDataType, StringIndexedWriteUpdatesByte) {
  SimFixture f;
  auto* s = RunAndFindVar(
      "module m;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = \"abc\";\n"
      "    s[1] = \"B\";\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "aBc");
}

TEST(StringDataType, AssignZeroToStringCharIgnored) {
  SimFixture f;
  auto* s = RunAndFindVar(
      "module m;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = \"abc\";\n"
      "    s[1] = 0;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "abc");
}

TEST(StringDataType, IndexOutOfRangeReturnsZero) {
  SimFixture f;
  MakeStringVar(f, "s", "abc");
  auto* sel =
      MakeSelectExpr(f.arena, MakeId(f.arena, "s"), MakeInt(f.arena, 10));
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(StringDataType, IntegralCastToStringZeroPadsThenStripsZeros) {
  SimFixture f;
  auto* s2 = RunAndFindVar(
      "module m;\n"
      "  bit [11:0] b = 12'ha41;\n"
      "  string s2;\n"
      "  initial s2 = string'(b);\n"
      "endmodule\n",
      f, "s2");
  ASSERT_NE(s2, nullptr);
  EXPECT_EQ(VecToStr(s2->value), "\nA");
}

TEST(StringDataType, DefaultStringVariableIndexingReturnsZero) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module m;\n"
      "  string s;\n"
      "  byte b;\n"
      "  initial b = s[0];\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64() & 0xFFu, 0u);
}

TEST(StringDataType, StringLiteralImplicitlyConvertedInEquality) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module m;\n"
      "  string a;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = \"hello\";\n"
      "    r = (a == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

TEST(StringDataType, ZeroMultiplierStringReplicationIsEmpty) {
  SimFixture f;
  auto* s = RunAndFindVar(
      "module m;\n"
      "  string s;\n"
      "  initial s = {\"x\", {0{\"ab\"}}, \"y\"};\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "xy");
}

TEST(StringDataType, StringLiteralToExactWidthIntegral) {
  SimFixture f;
  auto* c = RunAndFindVar(
      "module m;\n"
      "  byte c;\n"
      "  initial c = \"A\";\n"
      "endmodule\n",
      f, "c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64() & 0xFFu, 0x41u);
}

TEST(StringDataType, StringLiteralToWiderIntegralZeroFillsLeft) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module m;\n"
      "  bit [10:0] b;\n"
      "  initial b = \"A\";\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.width, 11u);
  EXPECT_EQ(b->value.ToUint64(), 0x41u);
}

TEST(StringDataType, StringLiteralToNarrowerIntegralTruncatesLeft) {
  SimFixture f;
  auto* h = RunAndFindVar(
      "module m;\n"
      "  bit [31:0] h;\n"
      "  initial h = \"hello\";\n"
      "endmodule\n",
      f, "h");
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(VecToStr(h->value), "ello");
}

TEST(StringDataType, NonConstantMultiplierStringReplication) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int i = 3;\n"
      "  string s;\n"
      "  initial s = {i{\"ab\"}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s = f.ctx.FindVariable("s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "ababab");
}

TEST(StringDataType, StringRelationalLessThanFullPipeline) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module m;\n"
      "  string a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = \"abc\";\n"
      "    b = \"abd\";\n"
      "    r = (a < b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

TEST(StringDataType, AllStringLiteralConcatenationAsIntegral) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module m;\n"
      "  bit [15:0] x;\n"
      "  initial x = {\"A\", \"B\"};\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x4142u);
}

TEST(StringDataType, StringLiteralAllZerosBecomesEmpty) {
  SimFixture f;
  auto* s = RunAndFindVar(
      "module m;\n"
      "  string s = \"\\0\";\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "");
}

TEST(StringDataType, BothStringLiteralsEqualityIsIntegral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic r_eq, r_ne;\n"
      "  initial begin\n"
      "    r_eq = (\"abc\" == \"abc\");\n"
      "    r_ne = (\"abc\" == \"abd\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r_eq = f.ctx.FindVariable("r_eq");
  auto* r_ne = f.ctx.FindVariable("r_ne");
  ASSERT_NE(r_eq, nullptr);
  ASSERT_NE(r_ne, nullptr);
  EXPECT_EQ(r_eq->value.ToUint64(), 1u);
  EXPECT_EQ(r_ne->value.ToUint64(), 0u);
}

TEST(StringDataType, MixedStringExprAndLiteralConcatenation) {
  SimFixture f;
  auto* c = RunAndFindVar(
      "module m;\n"
      "  string a, c;\n"
      "  initial begin\n"
      "    a = \"foo\";\n"
      "    c = {a, \"bar\"};\n"
      "  end\n"
      "endmodule\n",
      f, "c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(VecToStr(c->value), "foobar");
}

TEST(StringDataType, AllLiteralConcatAssignedToStringConverts) {
  SimFixture f;
  auto* s = RunAndFindVar(
      "module m;\n"
      "  string s;\n"
      "  initial s = {\"A\", \"B\"};\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "AB");
}

TEST(StringDataType, StringIndexLeftmostAndRightmostFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  byte first, last;\n"
      "  initial begin\n"
      "    s = \"hello\";\n"
      "    first = s[0];\n"
      "    last = s[4];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* first = f.ctx.FindVariable("first");
  auto* last = f.ctx.FindVariable("last");
  ASSERT_NE(first, nullptr);
  ASSERT_NE(last, nullptr);
  EXPECT_EQ(first->value.ToUint64() & 0xFFu, 0x68u);
  EXPECT_EQ(last->value.ToUint64() & 0xFFu, 0x6Fu);
}

TEST(StringDataType, UninitializedStringDefaultsToEmpty) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module m;\n"
      "  string s;\n"
      "  logic r;\n"
      "  initial r = (s == \"\");\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

TEST(StringDataType, StringExpressionInitializer) {
  SimFixture f;
  auto* s = RunAndFindVar(
      "module m;\n"
      "  string s = {\"foo\", \"bar\"};\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "foobar");
}

TEST(StringDataType, RelationalLessThanWithStringLiteralOperand) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module m;\n"
      "  string a;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = \"abc\";\n"
      "    r = (a < \"abd\");\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

TEST(StringDataType,
     StringParameterLongerThanFourCharactersKeepsEveryCharacter) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  parameter string NAME = \"John Smith\";\n"
      "  initial $display(\"%s\", NAME);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "John Smith\n");
}

TEST(StringDataType,
     StringParameterOfExactlyFiveCharactersKeepsEveryCharacter) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  parameter string S = \"hello\";\n"
      "  initial $display(\"%s\", S);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hello\n");
}

TEST(StringDataType, StringParameterIsRegisteredAsAStringVariable) {
  SimFixture f;
  auto* p = RunAndFindVar(
      "module m;\n"
      "  parameter string NAME = \"John Smith\";\n"
      "endmodule\n",
      f, "NAME");
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(f.ctx.IsStringVariable("NAME"));
}

TEST(StringDataType,
     AParameterInitializedFromAnotherStringParameterKeepsEveryCharacter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  parameter string A = \"John Smith\";\n"
                       "  parameter string B = A;\n"
                       "  initial $display(\"%s\", B);\n"
                       "endmodule\n",
                       f),
            "John Smith\n");
}

TEST(StringDataType,
     AParameterInitializedFromAStringConcatenationKeepsEveryCharacter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  parameter string B = {\"John\", \" Smith\"};\n"
                       "  initial $display(\"%s\", B);\n"
                       "endmodule\n",
                       f),
            "John Smith\n");
}

TEST(StringDataType,
     AParameterInitializedFromAStringReplicationKeepsEveryCharacter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  parameter string B = {3{\"ab\"}};\n"
                       "  initial $display(\"%s\", B);\n"
                       "endmodule\n",
                       f),
            "ababab\n");
}

TEST(StringDataType, AnElementOfAnArrayOfStringsDisplaysItsCharacters) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  string a [2];\n"
                       "  initial begin\n"
                       "    a[0] = \"planet\";\n"
                       "    $display(a[0]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "planet\n");
}

TEST(StringSim, AStringInOneTaskDoesNotMakeALikeNamedVariableAStringElsewhere) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  task mark();\n"
                       "    string tag;\n"
                       "    tag = \"x\";\n"
                       "  endtask\n"
                       "  task show();\n"
                       "    int tag;\n"
                       "    tag = 65;\n"
                       "    $display(tag);\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    mark();\n"
                       "    show();\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "         65\n");
}

TEST(StringSim, AStringDeclarationDoesNotOutliveTheBlockThatDeclaredIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  initial begin\n"
                       "    begin\n"
                       "      string s;\n"
                       "      s = \"x\";\n"
                       "    end\n"
                       "    begin\n"
                       "      int s;\n"
                       "      s = 66;\n"
                       "      $display(s);\n"
                       "    end\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "         66\n");
}

TEST(StringSim, AStringProductionNameDoesNotMarkALaterVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  int op;\n"
                       "  initial begin\n"
                       "    randsequence(main)\n"
                       "      void main : op ;\n"
                       "      string op : { return \"+\"; };\n"
                       "    endsequence\n"
                       "    op = 67;\n"
                       "    $display(op);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "         67\n");
}

TEST(StringSim, CharacterWriteIntoAnElementOfAnArrayOfStrings) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string sa[2];\n"
                       "  initial begin\n"
                       "    sa[0] = \"ab\"; sa[0][1] = \"X\";\n"
                       "    sa[1] = \"cd\"; sa[1][5] = \"Z\";\n"
                       "    $display(\"%s %s\", sa[0], sa[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "aX cd\n");
}

TEST(StringSim, LeafOfAMultidimensionalArrayOfStringsIsAString) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string m[2][2];\n"
                       "  initial begin\n"
                       "    m[1][0] = \"pq\";\n"
                       "    $write(\"%0d \", m[1][0].len());\n"
                       "    m[1][0][0] = \"P\";\n"
                       "    $display(\"%s\", m[1][0]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2 Pq\n");
}

}  // namespace
