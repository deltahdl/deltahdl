// Non-LRM tests

#include <cstring>
#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/sim_context.h"  // StructTypeInfo, StructFieldInfo

using namespace delta;

namespace {

TEST(EvalAdv, TaggedUnionNoTagSetAccessesNormally) {
  SimFixture f;
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
  auto* access_x = f.arena.Create<Expr>();
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
  SimFixture f;
  // tagged Valid 42 → evaluates to 42.
  auto* tagged = f.arena.Create<Expr>();
  tagged->kind = ExprKind::kTagged;
  auto* member = f.arena.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = "Valid";
  tagged->rhs = member;
  tagged->lhs = MakeInt(f.arena, 42);
  auto result = EvalExpr(tagged, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(EvalAdv, TaggedExprVoidMember) {
  SimFixture f;
  // tagged Invalid (void member, no value) → 0.
  auto* tagged = f.arena.Create<Expr>();
  tagged->kind = ExprKind::kTagged;
  auto* member = f.arena.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = "Invalid";
  tagged->rhs = member;
  tagged->lhs = nullptr;
  auto result = EvalExpr(tagged, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
