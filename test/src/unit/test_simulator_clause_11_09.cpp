#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

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

  auto* access_b = f.arena.Create<Expr>();
  access_b->kind = ExprKind::kMemberAccess;
  access_b->lhs = MakeId(f.arena, "u");
  access_b->rhs = MakeId(f.arena, "b");
  auto rb = EvalExpr(access_b, f.ctx, f.arena);
  EXPECT_NE(rb.words[0].bval, 0u);

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

// A read whose member name does not match the current tag must surface a
// run-time error diagnostic, not just return X bits.
TEST(TaggedUnionEval, MismatchedReadEmitsDiagnostic) {
  SimFixture f;

  StructTypeInfo uinfo;
  uinfo.type_name = "u_diag_r";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"a", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("u_diag_r", uinfo);

  MakeVar(f, "u", 8, 0x11);
  f.ctx.SetVariableStructType("u", "u_diag_r");
  f.ctx.SetVariableTag("u", "a");

  auto* access_b = f.arena.Create<Expr>();
  access_b->kind = ExprKind::kMemberAccess;
  access_b->lhs = MakeId(f.arena, "u");
  access_b->rhs = MakeId(f.arena, "b");

  EXPECT_FALSE(f.diag.HasErrors());
  (void)EvalExpr(access_b, f.ctx, f.arena);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A write through dot notation whose member name matches the current tag
// updates the union storage in place and raises no diagnostic.
TEST(TaggedUnionEval, MatchingMemberWriteUpdatesValue) {
  SimFixture f;

  StructTypeInfo uinfo;
  uinfo.type_name = "u_wr_ok";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"a", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("u_wr_ok", uinfo);

  auto* var = MakeVar(f, "u", 8, 0x00);
  f.ctx.SetVariableStructType("u", "u_wr_ok");
  f.ctx.SetVariableTag("u", "a");

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kMemberAccess;
  lhs->lhs = MakeId(f.arena, "u");
  lhs->rhs = MakeId(f.arena, "a");
  auto rhs_val = MakeLogic4VecVal(f.arena, 8, 0x5A);

  WriteStructField(lhs, rhs_val, f.ctx);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
}

// A write whose member name does not match the current tag must surface a
// run-time error diagnostic and leave the union storage unchanged.
TEST(TaggedUnionEval, MismatchedWriteEmitsDiagnosticAndKeepsValue) {
  SimFixture f;

  StructTypeInfo uinfo;
  uinfo.type_name = "u_diag_w";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"a", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("u_diag_w", uinfo);

  auto* var = MakeVar(f, "u", 8, 0x33);
  f.ctx.SetVariableStructType("u", "u_diag_w");
  f.ctx.SetVariableTag("u", "a");

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kMemberAccess;
  lhs->lhs = MakeId(f.arena, "u");
  lhs->rhs = MakeId(f.arena, "b");
  auto rhs_val = MakeLogic4VecVal(f.arena, 8, 0x77);

  EXPECT_FALSE(f.diag.HasErrors());
  WriteStructField(lhs, rhs_val, f.ctx);
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(var->value.ToUint64(), 0x33u);
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
