#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/const_eval.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct EvalFixture {
  SourceManager mgr;
  Arena arena;
};

static Expr* ParseExprFrom(const std::string& src, EvalFixture& f) {
  std::string code = "module t #(parameter P = " + src + ") (); endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  DiagEngine diag(f.mgr);
  Lexer lexer(f.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, f.arena, diag);
  auto* cu = parser.Parse();
  EXPECT_FALSE(cu->modules.empty());
  EXPECT_FALSE(cu->modules[0]->params.empty());
  return cu->modules[0]->params[0].second;
}

TEST(ConstEval, Arithmetic) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("3 + 4", f)), 7);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("10 - 3", f)), 7);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("6 * 7", f)), 42);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("15 / 3", f)), 5);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("17 % 5", f)), 2);
}

TEST(ConstEval, DivisionByZero) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("5 / 0", f)), std::nullopt);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("5 % 0", f)), std::nullopt);
}

TEST(ConstEval, Bitwise) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("12 & 10", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("12 | 3", f)), 15);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("5 ^ 3", f)), 6);
}

TEST(ConstEval, Shifts) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 << 4", f)), 16);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("16 >> 2", f)), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 <<< 4", f)), 16);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("16 >>> 2", f)), 4);
}

TEST(ConstEval, Comparison) {
  EvalFixture f;
  struct Case {
    const char* expr;
    int64_t expected;
  };
  const Case kCases[] = {
      {"3 < 5", 1},  {"5 < 3", 0},  {"5 > 3", 1}, {"3 >= 3", 1},
      {"3 <= 3", 1}, {"3 == 3", 1}, {"3 != 4", 1},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(ConstEvalInt(ParseExprFrom(c.expr, f)), c.expected) << c.expr;
  }
}

TEST(ConstEval, Logical) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 && 1", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 && 0", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 || 1", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 || 0", f)), 0);
}

TEST(ConstEval, Unary) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("-5", f)), -5);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("!0", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("!5", f)), 0);
}

TEST(ConstEval, Power) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("2 ** 10", f)), 1024);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("3 ** 0", f)), 1);
}

TEST(ConstEval, Ternary) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 ? 42 : 99", f)), 42);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 ? 42 : 99", f)), 99);
}

TEST(ConstEval, ScopedIdentifier) {
  EvalFixture f;
  ScopeMap scope = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH", f), scope), 16);
}

TEST(ConstEval, ScopedExprWithParam) {
  EvalFixture f;
  ScopeMap scope = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH > 8", f), scope), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH + 4", f), scope), 20);
}

TEST(ConstEval, ScopedUnresolved) {
  EvalFixture f;
  ScopeMap scope = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("UNKNOWN", f), scope), std::nullopt);
}

TEST(ConstEval, ScopedTernary) {
  EvalFixture f;
  ScopeMap scope_big = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH > 8 ? WIDTH : 8", f), scope_big),
            16);
  ScopeMap scope_small = {{"WIDTH", 4}};
  EXPECT_EQ(
      ConstEvalInt(ParseExprFrom("WIDTH > 8 ? WIDTH : 8", f), scope_small), 8);
}

TEST(ConstEval, Concatenation) {
  EvalFixture f;
  // {4'd3, 4'd5} = 8'h35 = 53
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{4'd3, 4'd5}", f)), 0x35);
}

TEST(ConstEval, Replication) {
  EvalFixture f;
  // {4{1'b1}} = 4'b1111 = 15
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{4{1'b1}}", f)), 15);
}

TEST(ConstEval, Clog2) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(256)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(1)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(5)", f)), 3);
}

TEST(ConstEval, BitsExpr) {
  EvalFixture f;
  // §20.6.2: $bits(8'hFF) should return 8 (width of expression).
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(8'hFF)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(16'h0)", f)), 16);
}

// ==========================================================================
// §11.5.3: Longest static prefix
// ==========================================================================

// Helper: build a simple identifier expression.
static Expr* LspId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Helper: build a select expression: base[index].
static Expr* LspSelect(Arena& arena, Expr* base, Expr* index) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = index;
  return e;
}

// Helper: build an integer literal.
static Expr* LspInt(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

TEST(ConstEval, LongestStaticPrefixSimpleId) {
  Arena arena;
  // Plain identifier "m" → prefix is "m".
  EXPECT_EQ(LongestStaticPrefix(LspId(arena, "m")), "m");
}

TEST(ConstEval, LongestStaticPrefixConstIdx) {
  Arena arena;
  // m[1] where 1 is constant → prefix is "m[1]".
  auto* sel = LspSelect(arena, LspId(arena, "m"), LspInt(arena, 1));
  EXPECT_EQ(LongestStaticPrefix(sel), "m[1]");
}

TEST(ConstEval, LongestStaticPrefixVarIdx) {
  Arena arena;
  // m[i] where i is not constant → prefix is "m".
  auto* sel = LspSelect(arena, LspId(arena, "m"), LspId(arena, "i"));
  EXPECT_EQ(LongestStaticPrefix(sel), "m");
}

TEST(ConstEval, LongestStaticPrefixNested) {
  Arena arena;
  // m[1][i] → m[1] is static, [i] is not → prefix is "m[1]".
  auto* inner = LspSelect(arena, LspId(arena, "m"), LspInt(arena, 1));
  auto* outer = LspSelect(arena, inner, LspId(arena, "i"));
  EXPECT_EQ(LongestStaticPrefix(outer), "m[1]");
}

TEST(ConstEval, LongestStaticPrefixParamIdx) {
  Arena arena;
  // m[P] where P=7 in scope → prefix is "m[7]".
  ScopeMap scope = {{"P", 7}};
  auto* sel = LspSelect(arena, LspId(arena, "m"), LspId(arena, "P"));
  EXPECT_EQ(LongestStaticPrefix(sel, scope), "m[7]");
}

// ==========================================================================
// §6.8: Implicit signedness of integer types
// ==========================================================================

// ==========================================================================
// §13.4.3 / §20.9: Constant system functions
// ==========================================================================

TEST(ConstEval, Countones) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(8'b10110010)", f)), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(8'b00000000)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(8'b11111111)", f)), 8);
}

TEST(ConstEval, Onehot) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00000001)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00001000)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00000000)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00010010)", f)), 0);
}

TEST(ConstEval, Onehot0) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(8'b00000001)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(8'b00000000)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(8'b00010010)", f)), 0);
}

#include "elaboration/type_eval.h"

TEST(TypeEval, ImplicitlySignedTypes) {
  // §6.8: integer, int, shortint, longint, byte are implicitly signed.
  // logic, reg, bit are NOT implicitly signed.
  struct Case {
    DataTypeKind kind;
    bool expected;
    const char* label;
  };
  const Case kCases[] = {
      {DataTypeKind::kInteger, true, "integer"},
      {DataTypeKind::kInt, true, "int"},
      {DataTypeKind::kShortint, true, "shortint"},
      {DataTypeKind::kLongint, true, "longint"},
      {DataTypeKind::kByte, true, "byte"},
      {DataTypeKind::kLogic, false, "logic"},
      {DataTypeKind::kReg, false, "reg"},
      {DataTypeKind::kBit, false, "bit"},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(IsImplicitlySigned(c.kind), c.expected) << c.label;
  }
}
