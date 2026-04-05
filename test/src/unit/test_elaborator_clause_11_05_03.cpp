#include <gtest/gtest.h>

#include <unordered_set>

#include "builders_ast.h"
#include "builders_sensitivity.h"
#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/sensitivity.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// Helper: build a kMemberAccess node (field select / hierarchical reference).
Expr* MakeMember(Arena& arena, Expr* obj, std::string_view field) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kMemberAccess;
  e->lhs = obj;
  e->rhs = MakeId(arena, field);
  return e;
}

// --- Edge cases ---

TEST(ConstEval, LongestStaticPrefixNullExpr) {
  EXPECT_EQ(LongestStaticPrefix(nullptr), "");
}

TEST(ConstEval, LongestStaticPrefixNonSelectExpr) {
  Arena arena;
  auto* bin = MakeBinary(arena, TokenKind::kPlus, MakeId(arena, "a"),
                         MakeId(arena, "b"));
  EXPECT_EQ(LongestStaticPrefix(bin), "");
}

TEST(ConstEval, LongestStaticPrefixAllConstMultiDim) {
  Arena arena;
  auto* inner = MakeSelectExpr(arena, MakeId(arena, "m"), MakeInt(arena, 1));
  auto* outer = MakeSelectExpr(arena, inner, MakeInt(arena, 2));
  EXPECT_EQ(LongestStaticPrefix(outer), "m[1][2]");
}

TEST(ConstEval, LongestStaticPrefixAllVarMultiDim) {
  Arena arena;
  auto* inner = MakeSelectExpr(arena, MakeId(arena, "m"), MakeId(arena, "i"));
  auto* outer = MakeSelectExpr(arena, inner, MakeId(arena, "j"));
  EXPECT_EQ(LongestStaticPrefix(outer), "m");
}

// --- Existing tests ---

TEST(ConstEval, LongestStaticPrefixSimpleId) {
  Arena arena;

  EXPECT_EQ(LongestStaticPrefix(MakeId(arena, "m")), "m");
}

TEST(ConstEval, LongestStaticPrefixConstIdx) {
  Arena arena;

  auto* sel = MakeSelectExpr(arena, MakeId(arena, "m"), MakeInt(arena, 1));
  EXPECT_EQ(LongestStaticPrefix(sel), "m[1]");
}

TEST(ConstEval, LongestStaticPrefixVarIdx) {
  Arena arena;

  auto* sel = MakeSelectExpr(arena, MakeId(arena, "m"), MakeId(arena, "i"));
  EXPECT_EQ(LongestStaticPrefix(sel), "m");
}

TEST(ConstEval, LongestStaticPrefixNested) {
  Arena arena;

  auto* inner = MakeSelectExpr(arena, MakeId(arena, "m"), MakeInt(arena, 1));
  auto* outer = MakeSelectExpr(arena, inner, MakeId(arena, "i"));
  EXPECT_EQ(LongestStaticPrefix(outer), "m[1]");
}

TEST(ConstEval, LongestStaticPrefixParamIdx) {
  Arena arena;

  ScopeMap scope = {{"P", 7}};
  auto* sel = MakeSelectExpr(arena, MakeId(arena, "m"), MakeId(arena, "P"));
  EXPECT_EQ(LongestStaticPrefix(sel, scope), "m[7]");
}

TEST(Sensitivity, SelectConstIdxUsesLSP) {
  Arena arena;
  auto* expr = SensSelect(arena, SensId(arena, "a"), SensIntLit(arena, 1));
  std::unordered_set<std::string> reads;
  CollectExprReads(expr, reads);
  EXPECT_TRUE(reads.count("a[1]"));
  EXPECT_FALSE(reads.count("a"));
}

TEST(Sensitivity, NestedSelectUsesLSP) {
  Arena arena;
  auto* inner = SensSelect(arena, SensId(arena, "a"), SensIntLit(arena, 1));
  auto* outer = SensSelect(arena, inner, SensId(arena, "i"));
  std::unordered_set<std::string> reads;
  CollectExprReads(outer, reads);
  EXPECT_TRUE(reads.count("a[1]"));
  EXPECT_TRUE(reads.count("i"));
  EXPECT_FALSE(reads.count("a"));
}

TEST(Sensitivity, SelectVarIdxUsesLSP) {
  Arena arena;
  auto* expr = SensSelect(arena, SensId(arena, "a"), SensId(arena, "i"));
  std::unordered_set<std::string> reads;
  CollectExprReads(expr, reads);
  EXPECT_TRUE(reads.count("a"));
  EXPECT_TRUE(reads.count("i"));
}

// --- Field selects as static prefixes ---

TEST(ConstEval, LongestStaticPrefixFieldSelect) {
  Arena arena;
  auto* expr = MakeMember(arena, MakeId(arena, "s"), "field");
  EXPECT_EQ(LongestStaticPrefix(expr), "s.field");
}

TEST(ConstEval, LongestStaticPrefixFieldSelectThenConstIdx) {
  Arena arena;
  auto* field = MakeMember(arena, MakeId(arena, "s"), "field");
  auto* sel = MakeSelectExpr(arena, field, MakeInt(arena, 1));
  EXPECT_EQ(LongestStaticPrefix(sel), "s.field[1]");
}

TEST(ConstEval, LongestStaticPrefixConstIdxThenFieldSelect) {
  Arena arena;
  auto* sel = MakeSelectExpr(arena, MakeId(arena, "arr"), MakeInt(arena, 1));
  auto* expr = MakeMember(arena, sel, "field");
  EXPECT_EQ(LongestStaticPrefix(expr), "arr[1].field");
}

TEST(ConstEval, LongestStaticPrefixVarIdxThenFieldSelect) {
  Arena arena;
  auto* sel = MakeSelectExpr(arena, MakeId(arena, "arr"), MakeId(arena, "i"));
  auto* expr = MakeMember(arena, sel, "field");
  EXPECT_EQ(LongestStaticPrefix(expr), "arr");
}

// --- Package references as static prefixes ---

TEST(ConstEval, LongestStaticPrefixPackageRef) {
  Arena arena;
  auto* id = MakeId(arena, "var");
  id->scope_prefix = "pkg::";
  EXPECT_EQ(LongestStaticPrefix(id), "pkg::var");
}

TEST(ConstEval, LongestStaticPrefixPackageRefConstIdx) {
  Arena arena;
  auto* id = MakeId(arena, "arr");
  id->scope_prefix = "pkg::";
  auto* sel = MakeSelectExpr(arena, id, MakeInt(arena, 3));
  EXPECT_EQ(LongestStaticPrefix(sel), "pkg::arr[3]");
}

// --- Sensitivity integration for field selects ---

TEST(Sensitivity, FieldSelectVarIdxUsesLSP) {
  Arena arena;
  auto* field = MakeMember(arena, SensId(arena, "s"), "field");
  auto* expr = SensSelect(arena, field, SensId(arena, "i"));
  std::unordered_set<std::string> reads;
  CollectExprReads(expr, reads);
  EXPECT_TRUE(reads.count("s.field"));
  EXPECT_TRUE(reads.count("i"));
}

}  // namespace
