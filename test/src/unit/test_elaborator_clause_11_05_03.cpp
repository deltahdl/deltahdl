// §11.5.3: Longest static prefix

#include <gtest/gtest.h>
#include "common/arena.h"
#include "elaboration/const_eval.h"
#include "parser/ast.h"

using namespace delta;

static Expr* LspId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Expr* LspSelect(Arena& arena, Expr* base, Expr* index) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = index;
  return e;
}

static Expr* LspInt(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

namespace {

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

static Expr *SensId(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Expr *SensSelect(Arena &arena, Expr *base, Expr *index) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = index;
  return e;
}

static Expr *SensIntLit(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

TEST(Sensitivity, SelectConstIdxUsesLSP) {
  // a[1] → LSP is "a[1]", sensitivity should include "a[1]" not "a".
  Arena arena;
  auto *expr = SensSelect(arena, SensId(arena, "a"), SensIntLit(arena, 1));
  std::unordered_set<std::string> reads;
  CollectExprReads(expr, reads);
  EXPECT_TRUE(reads.count("a[1]"));
  EXPECT_FALSE(reads.count("a"));
}

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

TEST(Sensitivity, SelectVarIdxUsesLSP) {
  // a[i] → LSP is "a", sensitivity includes "a" and "i".
  Arena arena;
  auto *expr = SensSelect(arena, SensId(arena, "a"), SensId(arena, "i"));
  std::unordered_set<std::string> reads;
  CollectExprReads(expr, reads);
  EXPECT_TRUE(reads.count("a"));
  EXPECT_TRUE(reads.count("i"));
}

TEST(Sensitivity, NestedSelectUsesLSP) {
  // a[1][i] → LSP is "a[1]", sensitivity includes "a[1]" and "i".
  Arena arena;
  auto *inner = SensSelect(arena, SensId(arena, "a"), SensIntLit(arena, 1));
  auto *outer = SensSelect(arena, inner, SensId(arena, "i"));
  std::unordered_set<std::string> reads;
  CollectExprReads(outer, reads);
  EXPECT_TRUE(reads.count("a[1]"));
  EXPECT_TRUE(reads.count("i"));
  EXPECT_FALSE(reads.count("a"));
}

}  // namespace
