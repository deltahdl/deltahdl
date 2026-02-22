// §11.9: Tagged union expressions and member access

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h" // StructTypeInfo, StructFieldInfo
#include <cstring>
#include <gtest/gtest.h>

using namespace delta;

// Shared fixture for advanced expression evaluation tests (§11 phases 22+).
struct EvalAdvFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr *MakeInt(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

static Expr *MakeId(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Variable *MakeVar(EvalAdvFixture &f, std::string_view name,
                         uint32_t width, uint64_t val) {
  auto *var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  return var;
}

namespace {

// ==========================================================================
// §11.9: Tagged union — tag mismatch returns X
// ==========================================================================
TEST(EvalAdv, TaggedUnionMismatchReturnsX) {
  EvalAdvFixture f;
  // Create a tagged union type with members a (8-bit) and b (8-bit).
  StructTypeInfo uinfo;
  uinfo.type_name = "tagged_u";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"a", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("tagged_u", uinfo);

  // Create variable "u" with value 0x42 and tag "a".
  MakeVar(f, "u", 8, 0x42);
  f.ctx.SetVariableStructType("u", "tagged_u");
  f.ctx.SetVariableTag("u", "a");

  // Access u.a — tag matches, should return 0x42.
  auto *access_a = f.arena.Create<Expr>();
  access_a->kind = ExprKind::kMemberAccess;
  access_a->lhs = MakeId(f.arena, "u");
  access_a->rhs = MakeId(f.arena, "a");
  auto result_a = EvalExpr(access_a, f.ctx, f.arena);
  EXPECT_EQ(result_a.ToUint64(), 0x42u);

  // Access u.b — tag mismatch (active tag is "a"), should return X.
  auto *access_b = f.arena.Create<Expr>();
  access_b->kind = ExprKind::kMemberAccess;
  access_b->lhs = MakeId(f.arena, "u");
  access_b->rhs = MakeId(f.arena, "b");
  auto result_b = EvalExpr(access_b, f.ctx, f.arena);
  // X means bval all-1s.
  EXPECT_NE(result_b.nwords, 0u);
  EXPECT_NE(result_b.words[0].bval, 0u);
}

TEST(EvalAdv, TaggedUnionNoTagSetAccessesNormally) {
  EvalAdvFixture f;
  // Union without a tag set should still allow access.
  StructTypeInfo uinfo;
  uinfo.type_name = "simple_u";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"x", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("simple_u", uinfo);

  MakeVar(f, "v", 8, 0xFF);
  f.ctx.SetVariableStructType("v", "simple_u");
  // No tag set — access v.x should return the value normally.
  auto *access_x = f.arena.Create<Expr>();
  access_x->kind = ExprKind::kMemberAccess;
  access_x->lhs = MakeId(f.arena, "v");
  access_x->rhs = MakeId(f.arena, "x");
  auto result_x = EvalExpr(access_x, f.ctx, f.arena);
  EXPECT_EQ(result_x.ToUint64(), 0xFFu);
}

// ==========================================================================
// §11.9: Tagged union expressions
// ==========================================================================
TEST(EvalAdv, TaggedExprWithValue) {
  EvalAdvFixture f;
  // tagged Valid 42 → evaluates to 42.
  auto *tagged = f.arena.Create<Expr>();
  tagged->kind = ExprKind::kTagged;
  auto *member = f.arena.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = "Valid";
  tagged->rhs = member;
  tagged->lhs = MakeInt(f.arena, 42);
  auto result = EvalExpr(tagged, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(EvalAdv, TaggedExprVoidMember) {
  EvalAdvFixture f;
  // tagged Invalid (void member, no value) → 0.
  auto *tagged = f.arena.Create<Expr>();
  tagged->kind = ExprKind::kTagged;
  auto *member = f.arena.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = "Invalid";
  tagged->rhs = member;
  tagged->lhs = nullptr;
  auto result = EvalExpr(tagged, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

} // namespace
