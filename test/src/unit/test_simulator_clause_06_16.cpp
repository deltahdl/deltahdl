#include <cstdint>
#include <cstring>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/adv_sim.h"
#include "simulator/evaluation.h"

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

static std::string VecToStr(const Logic4Vec& vec) {
  std::string result;
  uint32_t nbytes = vec.width / 8;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    auto ch = static_cast<char>((vec.words[word].aval >> bit) & 0xFF);
    result.push_back(ch);
  }
  return result;
}

static Variable* MakeStringVar(SimFixture& f, std::string_view name,
                               std::string_view value) {
  uint32_t width = static_cast<uint32_t>(value.size()) * 8;
  if (width == 0) width = 8;
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  for (size_t i = 0; i < value.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(value.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    var->value.words[word].aval |=
        static_cast<uint64_t>(static_cast<unsigned char>(value[i])) << bit;
  }
  f.ctx.RegisterStringVariable(name);
  return var;
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

TEST(StringDataType, StringRelationalLessThan) {
  SimFixture f;
  MakeStringVar(f, "a", "abc");
  MakeStringVar(f, "b", "def");
  auto* lt = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "a"),
                        MakeId(f.arena, "b"));
  auto result = EvalExpr(lt, f.ctx, f.arena);
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

TEST(StringDataType, StringIndexReturnsAscii) {
  SimFixture f;
  MakeStringVar(f, "s", "hello");
  auto* sel =
      MakeSelectExpr(f.arena, MakeId(f.arena, "s"), MakeInt(f.arena, 0));
  auto result = EvalExpr(sel, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0x68u);
}

TEST(StringDataType, StringAssignFromString) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  initial begin\n"
      "    a = \"test\";\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var_b = f.ctx.FindVariable("b");
  ASSERT_NE(var_b, nullptr);
  EXPECT_EQ(VecToStr(var_b->value), "test");
}

TEST(StringDataType, StringLiteralEmbeddedZeroStrippedInInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s1 = \"hello\\0world\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s1 = f.ctx.FindVariable("s1");
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(VecToStr(s1->value), "helloworld");
}

TEST(StringDataType, StringLiteralEmbeddedZeroStrippedInProceduralAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = \"foo\\0bar\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s = f.ctx.FindVariable("s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "foobar");
}

TEST(StringDataType, StringIndexedWriteUpdatesByte) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = \"abc\";\n"
      "    s[1] = \"B\";\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s = f.ctx.FindVariable("s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "aBc");
}

TEST(StringDataType, AssignZeroToStringCharIgnored) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = \"abc\";\n"
      "    s[1] = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s = f.ctx.FindVariable("s");
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

TEST(StringDataType, IndexEmptyStringIsOutOfBounds) {
  SimFixture f;
  MakeStringVar(f, "s", "");
  auto* sel =
      MakeSelectExpr(f.arena, MakeId(f.arena, "s"), MakeInt(f.arena, 0));
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(StringDataType, IntegralCastToStringZeroPadsThenStripsZeros) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [11:0] b = 12'ha41;\n"
      "  string s2;\n"
      "  initial s2 = string'(b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s2 = f.ctx.FindVariable("s2");
  ASSERT_NE(s2, nullptr);
  EXPECT_EQ(VecToStr(s2->value), "\nA");
}

TEST(StringDataType, StringConcatenationProducesStringResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string a, b, c;\n"
      "  initial begin\n"
      "    a = \"foo\";\n"
      "    b = \"bar\";\n"
      "    c = {a, b};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(VecToStr(c->value), "foobar");
}

TEST(StringDataType, StringReplicationOperator) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = {3{\"ab\"}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s = f.ctx.FindVariable("s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "ababab");
}

TEST(StringDataType, DefaultStringVariableIndexingReturnsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  byte b;\n"
      "  initial b = s[0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64() & 0xFFu, 0u);
}

TEST(StringDataType, StringLiteralImplicitlyConvertedInEquality) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string a;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = \"hello\";\n"
      "    r = (a == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

// §6.16, Table 6-9: a string replication with a zero multiplier produces
// the empty string, so it contributes nothing to an enclosing string
// concatenation.
TEST(StringDataType, ZeroMultiplierStringReplicationIsEmpty) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = {\"x\", {0{\"ab\"}}, \"y\"};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s = f.ctx.FindVariable("s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "xy");
}

// §6.16: a string literal assigned to an integral variable whose width
// equals the literal width is stored unchanged.
TEST(StringDataType, StringLiteralToExactWidthIntegral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte c;\n"
      "  initial c = \"A\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64() & 0xFFu, 0x41u);
}

// §6.16: assigning a narrower string literal to a wider integral variable
// right justifies it and zero-fills on the left.
TEST(StringDataType, StringLiteralToWiderIntegralZeroFillsLeft) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [10:0] b;\n"
      "  initial b = \"A\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.width, 11u);
  EXPECT_EQ(b->value.ToUint64(), 0x41u);
}

// §6.16: assigning a wider string literal to a narrower integral variable
// right justifies it and truncates on the left (dropping the leading
// characters, not the trailing ones).
TEST(StringDataType, StringLiteralToNarrowerIntegralTruncatesLeft) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [31:0] h;\n"
      "  initial h = \"hello\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* h = f.ctx.FindVariable("h");
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(VecToStr(h->value), "ello");
}

}  // namespace
