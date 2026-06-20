#include <gtest/gtest.h>

#include "builders_ast.h"
#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "parser/ast.h"

using namespace delta;

namespace {

Expr* MakeMember(Arena& arena, Expr* obj, std::string_view field) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kMemberAccess;
  e->lhs = obj;
  e->rhs = MakeId(arena, field);
  return e;
}

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

TEST(ConstEval, LongestStaticPrefixHierarchicalRef) {
  Arena arena;
  // A multi-level dotted reference (e.g. top.sub.sig) is a hierarchical
  // reference to an object; the whole chain is a static prefix.
  auto* sub = MakeMember(arena, MakeId(arena, "top"), "sub");
  auto* sig = MakeMember(arena, sub, "sig");
  EXPECT_EQ(LongestStaticPrefix(sig), "top.sub.sig");
}

TEST(ConstEval, LongestStaticPrefixHierarchicalRefConstIdx) {
  Arena arena;
  // A constant index applied to a hierarchical reference stays inside the
  // static prefix.
  auto* mem =
      MakeMember(arena, MakeMember(arena, MakeId(arena, "top"), "sub"), "mem");
  auto* sel = MakeSelectExpr(arena, mem, MakeInt(arena, 2));
  EXPECT_EQ(LongestStaticPrefix(sel), "top.sub.mem[2]");
}

TEST(ConstEval, LongestStaticPrefixHierarchicalRefVarIdx) {
  Arena arena;
  // A variable index breaks the static prefix back to the hierarchical name.
  auto* mem =
      MakeMember(arena, MakeMember(arena, MakeId(arena, "top"), "sub"), "mem");
  auto* sel = MakeSelectExpr(arena, mem, MakeId(arena, "i"));
  EXPECT_EQ(LongestStaticPrefix(sel), "top.sub.mem");
}

TEST(ConstEval, LongestStaticPrefixParamThenConstIdx) {
  Arena arena;
  // LRM example: m[p][1] with localparam p = 7. Both indices are constant, so
  // the whole select is a static prefix; the parameter resolves to its value.
  ScopeMap scope = {{"p", 7}};
  auto* inner = MakeSelectExpr(arena, MakeId(arena, "m"), MakeId(arena, "p"));
  auto* outer = MakeSelectExpr(arena, inner, MakeInt(arena, 1));
  EXPECT_EQ(LongestStaticPrefix(outer, scope), "m[7][1]");
}

TEST(ConstEval, LongestStaticPrefixVarThenConstIdx) {
  Arena arena;
  // LRM example: m[i][1]. The inner select is non-static, so a constant outer
  // index cannot extend the static prefix beyond the identifier.
  auto* inner = MakeSelectExpr(arena, MakeId(arena, "m"), MakeId(arena, "i"));
  auto* outer = MakeSelectExpr(arena, inner, MakeInt(arena, 1));
  EXPECT_EQ(LongestStaticPrefix(outer), "m");
}

TEST(ConstEval, LongestStaticPrefixConstExprIdx) {
  Arena arena;
  // The select expression may be any constant expression, not just a literal.
  auto* idx =
      MakeBinary(arena, TokenKind::kPlus, MakeInt(arena, 1), MakeInt(arena, 1));
  auto* sel = MakeSelectExpr(arena, MakeId(arena, "m"), idx);
  EXPECT_EQ(LongestStaticPrefix(sel), "m[2]");
}

TEST(ConstEval, LongestStaticPrefixIndexedPartSelectVarBase) {
  Arena arena;
  // An indexed part-select is an indexing select; with a base that can vary at
  // run time it is not a static prefix, so the prefix stops at the identifier.
  auto* sel = MakeSelectExpr(arena, MakeId(arena, "arr"), MakeId(arena, "i"));
  sel->index_end = MakeInt(arena, 4);
  sel->is_part_select_plus = true;
  EXPECT_EQ(LongestStaticPrefix(sel), "arr");
}

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

}  // namespace
