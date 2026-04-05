#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(TaggedUnionEval, TaggedUnionMismatchReturnsX) {
  SimFixture f;

  StructTypeInfo uinfo;
  uinfo.type_name = "tagged_u";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"a", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("tagged_u", uinfo);

  MakeVar(f, "u", 8, 0x42);
  f.ctx.SetVariableStructType("u", "tagged_u");
  f.ctx.SetVariableTag("u", "a");

  auto* access_a = f.arena.Create<Expr>();
  access_a->kind = ExprKind::kMemberAccess;
  access_a->lhs = MakeId(f.arena, "u");
  access_a->rhs = MakeId(f.arena, "a");
  auto result_a = EvalExpr(access_a, f.ctx, f.arena);
  EXPECT_EQ(result_a.ToUint64(), 0x42u);

  auto* access_b = f.arena.Create<Expr>();
  access_b->kind = ExprKind::kMemberAccess;
  access_b->lhs = MakeId(f.arena, "u");
  access_b->rhs = MakeId(f.arena, "b");
  auto result_b = EvalExpr(access_b, f.ctx, f.arena);

  EXPECT_NE(result_b.nwords, 0u);
  EXPECT_NE(result_b.words[0].bval, 0u);
}

TEST(TaggedUnionEval, TaggedUnionNoTagSetAccessesNormally) {
  SimFixture f;

  StructTypeInfo uinfo;
  uinfo.type_name = "simple_u";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"x", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("simple_u", uinfo);

  MakeVar(f, "v", 8, 0xFF);
  f.ctx.SetVariableStructType("v", "simple_u");

  auto* access_x = f.arena.Create<Expr>();
  access_x->kind = ExprKind::kMemberAccess;
  access_x->lhs = MakeId(f.arena, "v");
  access_x->rhs = MakeId(f.arena, "x");
  auto result_x = EvalExpr(access_x, f.ctx, f.arena);
  EXPECT_EQ(result_x.ToUint64(), 0xFFu);
}

TEST(TaggedUnionEval, TaggedExprWithValue) {
  SimFixture f;

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

TEST(TaggedUnionEval, TaggedExprVoidMember) {
  SimFixture f;

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

TEST(TaggedUnion, SetAndGetTag) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("u", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  f.ctx.SetVariableTag("u", "field_a");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "field_a");
}

TEST(TaggedUnion, OverwriteTagUpdatesActiveTag) {
  SimFixture f;
  f.ctx.CreateVariable("u", 32);
  f.ctx.SetVariableTag("u", "a");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "a");
  f.ctx.SetVariableTag("u", "b");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "b");
}

TEST(TaggedUnionEval, MatchingMemberReadReturnsValue) {
  SimFixture f;

  StructTypeInfo uinfo;
  uinfo.type_name = "u3";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 16;
  uinfo.fields.push_back({"x", 0, 16, DataTypeKind::kLogic});
  uinfo.fields.push_back({"y", 0, 16, DataTypeKind::kLogic});
  uinfo.fields.push_back({"z", 0, 16, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("u3", uinfo);

  MakeVar(f, "u", 16, 0xBEEF);
  f.ctx.SetVariableStructType("u", "u3");
  f.ctx.SetVariableTag("u", "y");

  auto* access = f.arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MakeId(f.arena, "u");
  access->rhs = MakeId(f.arena, "y");
  auto result = EvalExpr(access, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xBEEFu);
}

TEST(TaggedUnionEval, MismatchedMemberReadThreeMemberUnion) {
  SimFixture f;

  StructTypeInfo uinfo;
  uinfo.type_name = "u3";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"a", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"c", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("u3", uinfo);

  MakeVar(f, "u", 8, 0x55);
  f.ctx.SetVariableStructType("u", "u3");
  f.ctx.SetVariableTag("u", "a");

  // Access "b" while tag is "a" — should return X.
  auto* access_b = f.arena.Create<Expr>();
  access_b->kind = ExprKind::kMemberAccess;
  access_b->lhs = MakeId(f.arena, "u");
  access_b->rhs = MakeId(f.arena, "b");
  auto rb = EvalExpr(access_b, f.ctx, f.arena);
  EXPECT_NE(rb.words[0].bval, 0u);

  // Access "c" while tag is "a" — should also return X.
  auto* access_c = f.arena.Create<Expr>();
  access_c->kind = ExprKind::kMemberAccess;
  access_c->lhs = MakeId(f.arena, "u");
  access_c->rhs = MakeId(f.arena, "c");
  auto rc = EvalExpr(access_c, f.ctx, f.arena);
  EXPECT_NE(rc.words[0].bval, 0u);
}

TEST(TaggedUnionEval, TaggedExprWithSubExpr) {
  SimFixture f;

  auto* inner = MakeBinary(f.arena, TokenKind::kPlus, MakeInt(f.arena, 23),
                           MakeInt(f.arena, 34));
  auto* tagged = f.arena.Create<Expr>();
  tagged->kind = ExprKind::kTagged;
  tagged->rhs = MakeId(f.arena, "Valid");
  tagged->lhs = inner;
  auto result = EvalExpr(tagged, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 57u);
}

TEST(TaggedUnionEval, TaggedAssignSetsTag) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 7;\n"
      "    result = u.A;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(TaggedUnionEval, TaggedAssignOverwriteAndRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int X; int Y; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged X 100;\n"
      "    u = tagged Y 200;\n"
      "    result = u.Y;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 200u);
}

TEST(TaggedUnionEval, VoidMemberThenValueMember) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { void None; int Some; } Opt;\n"
      "  Opt o;\n"
      "  int result;\n"
      "  initial begin\n"
      "    o = tagged None;\n"
      "    o = tagged Some 77;\n"
      "    result = o.Some;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

}  // namespace
