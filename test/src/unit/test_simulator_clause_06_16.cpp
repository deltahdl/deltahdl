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

TEST(StringDataType, StringConcatValue) {
  SimFixture f;
  MakeStringVar(f, "s1", "hello");
  MakeStringVar(f, "s2", " world");
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "s1"));
  concat->elements.push_back(MakeId(f.arena, "s2"));
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(VecToStr(result), "hello world");
}

TEST(StringDataType, StringReplicateValue) {
  SimFixture f;
  MakeStringVar(f, "sr", "ab");
  auto* repl = f.arena.Create<Expr>();
  repl->kind = ExprKind::kReplicate;
  repl->repeat_count = MakeInt(f.arena, 3);
  repl->elements.push_back(MakeId(f.arena, "sr"));
  auto result = EvalExpr(repl, f.ctx, f.arena);
  EXPECT_EQ(VecToStr(result), "ababab");
}

TEST(StringDataType, StringConcatSetsIsString) {
  SimFixture f;
  MakeStringVar(f, "sa", "hi");
  MakeStringVar(f, "sb", "lo");
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "sa"));
  concat->elements.push_back(MakeId(f.arena, "sb"));
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_TRUE(result.is_string);
}

TEST(StringDataType, NonStringConcatNotIsString) {
  SimFixture f;
  auto* a = f.ctx.CreateVariable("ia", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 0x41);
  auto* b = f.ctx.CreateVariable("ib", 8);
  b->value = MakeLogic4VecVal(f.arena, 8, 0x42);
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "ia"));
  concat->elements.push_back(MakeId(f.arena, "ib"));
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_FALSE(result.is_string);
}

TEST(StringDataType, StringReplicateSetsIsString) {
  SimFixture f;
  MakeStringVar(f, "sr2", "ab");
  auto* repl = f.arena.Create<Expr>();
  repl->kind = ExprKind::kReplicate;
  repl->repeat_count = MakeInt(f.arena, 2);
  repl->elements.push_back(MakeId(f.arena, "sr2"));
  auto result = EvalExpr(repl, f.ctx, f.arena);
  EXPECT_TRUE(result.is_string);
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
  auto* ne = MakeBinary(f.arena, TokenKind::kBangEq,
                         MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(ne, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(StringDataType, StringEqualityOpSameValue) {
  SimFixture f;
  MakeStringVar(f, "a", "hello");
  MakeStringVar(f, "b", "hello");
  auto* eq = MakeBinary(f.arena, TokenKind::kEqEq,
                         MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(eq, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(StringDataType, StringRelationalLessThan) {
  SimFixture f;
  MakeStringVar(f, "a", "abc");
  MakeStringVar(f, "b", "def");
  auto* lt = MakeBinary(f.arena, TokenKind::kLt,
                         MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(lt, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(StringDataType, StringRelationalGreaterThan) {
  SimFixture f;
  MakeStringVar(f, "a", "xyz");
  MakeStringVar(f, "b", "abc");
  auto* gt = MakeBinary(f.arena, TokenKind::kGt,
                         MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(gt, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(StringDataType, StringRelationalLessEqual) {
  SimFixture f;
  MakeStringVar(f, "a", "abc");
  MakeStringVar(f, "b", "abc");
  auto* le = MakeBinary(f.arena, TokenKind::kLtEq,
                         MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(le, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(StringDataType, StringRelationalGreaterEqual) {
  SimFixture f;
  MakeStringVar(f, "a", "def");
  MakeStringVar(f, "b", "abc");
  auto* ge = MakeBinary(f.arena, TokenKind::kGtEq,
                         MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  auto result = EvalExpr(ge, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(StringDataType, StringIndexReturnsAscii) {
  SimFixture f;
  MakeStringVar(f, "s", "hello");
  auto* sel = MakeSelectExpr(f.arena, MakeId(f.arena, "s"), MakeInt(f.arena, 0));
  auto result = EvalExpr(sel, f.ctx, f.arena);
  // §6.16 Table 6-9: s[0] returns ASCII code of first character ('h' = 0x68).
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

}  // namespace
