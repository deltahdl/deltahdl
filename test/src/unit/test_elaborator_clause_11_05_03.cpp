// §11.5.3: Longest static prefix

#include <gtest/gtest.h>

#include "builders_ast.h"
#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "parser/ast.h"

using namespace delta;

namespace {

TEST(ConstEval, LongestStaticPrefixSimpleId) {
  Arena arena;
  // Plain identifier "m" → prefix is "m".
  EXPECT_EQ(LongestStaticPrefix(MakeId(arena, "m")), "m");
}

TEST(ConstEval, LongestStaticPrefixConstIdx) {
  Arena arena;
  // m[1] where 1 is constant → prefix is "m[1]".
  auto* sel = MakeSelectExpr(arena, MakeId(arena, "m"), MakeInt(arena, 1));
  EXPECT_EQ(LongestStaticPrefix(sel), "m[1]");
}

TEST(ConstEval, LongestStaticPrefixVarIdx) {
  Arena arena;
  // m[i] where i is not constant → prefix is "m".
  auto* sel = MakeSelectExpr(arena, MakeId(arena, "m"), MakeId(arena, "i"));
  EXPECT_EQ(LongestStaticPrefix(sel), "m");
}

TEST(ConstEval, LongestStaticPrefixNested) {
  Arena arena;
  // m[1][i] → m[1] is static, [i] is not → prefix is "m[1]".
  auto* inner = MakeSelectExpr(arena, MakeId(arena, "m"), MakeInt(arena, 1));
  auto* outer = MakeSelectExpr(arena, inner, MakeId(arena, "i"));
  EXPECT_EQ(LongestStaticPrefix(outer), "m[1]");
}

TEST(ConstEval, LongestStaticPrefixParamIdx) {
  Arena arena;
  // m[P] where P=7 in scope → prefix is "m[7]".
  ScopeMap scope = {{"P", 7}};
  auto* sel = MakeSelectExpr(arena, MakeId(arena, "m"), MakeId(arena, "P"));
  EXPECT_EQ(LongestStaticPrefix(sel, scope), "m[7]");
}

TEST(Sensitivity, SelectConstIdxUsesLSP) {
  // a[1] → LSP is "a[1]", sensitivity should include "a[1]" not "a".
  Arena arena;
  auto* expr = SensSelect(arena, SensId(arena, "a"), SensIntLit(arena, 1));
  std::unordered_set<std::string> reads;
  CollectExprReads(expr, reads);
  EXPECT_TRUE(reads.count("a[1]"));
  EXPECT_FALSE(reads.count("a"));
}

TEST(Sensitivity, NestedSelectUsesLSP) {
  // a[1][i] → LSP is "a[1]", sensitivity includes "a[1]" and "i".
  Arena arena;
  auto* inner = SensSelect(arena, SensId(arena, "a"), SensIntLit(arena, 1));
  auto* outer = SensSelect(arena, inner, SensId(arena, "i"));
  std::unordered_set<std::string> reads;
  CollectExprReads(outer, reads);
  EXPECT_TRUE(reads.count("a[1]"));
  EXPECT_TRUE(reads.count("i"));
  EXPECT_FALSE(reads.count("a"));
}

}  // namespace
