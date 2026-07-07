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

// §11.9: a variable of tagged union type can be initialized with a tagged union
// expression whose member value is a legal initializer for the member type. The
// declaration initializer (a syntactic position distinct from a procedural
// assignment) establishes the member value, read back through dot notation.
TEST(TaggedUnionEval, DeclarationInitializerHoldsMemberValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u = tagged A 5;\n"
      "  int result;\n"
      "  initial result = u.A;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

// §11.9: initializing a tagged-union variable with `tagged A ...` also
// establishes its active tag (like a procedural `u = tagged A ...`), so a later
// read of a different member is inconsistent with the current tag and must
// raise a run-time error. Drives the initializer tag-set path end to end.
TEST(TaggedUnionEval, DeclarationInitializerSetsTagForMemberCheck) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u = tagged A 5;\n"
      "  int result;\n"
      "  initial result = u.B;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §11.9: members of a tagged union are read using the usual dot notation and
// the read shall be consistent with the current tag. After a real procedural
// `u = tagged A ...` sets the tag, reading member B is inconsistent and raises
// a run-time error (tag produced by real source, not a hand-set fixture tag).
TEST(TaggedUnionEval, ProceduralAssignThenMismatchedReadErrors) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 5;\n"
      "    result = u.B;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §11.9: an uninitialized variable of tagged union type is undefined, which
// includes its tag bits — no member is current. Built from a real declaration
// with no initializer and observed after a run: the variable exists but carries
// no active tag.
TEST(TaggedUnionEval, UninitializedTaggedUnionHasNoActiveTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_NE(f.ctx.FindVariable("u"), nullptr);
  EXPECT_TRUE(f.ctx.GetVariableTag("u").empty());
}

// §11.9: the type of a tagged union expression may be supplied by a cast rather
// than by an assignment target. `U'(tagged A ...)` names the union type, so the
// tagged expression is evaluated in that context and yields its member value.
TEST(TaggedUnionEval, CastContextTaggedExprEvaluates) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = U'(tagged A 9);\n"
      "    result = u.A;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

// §11.9 + dependency §10.9.2: the member value of a tagged expression may be a
// structure assignment pattern. Built from real source (a struct-typed union
// member assigned `tagged Add '{...}`) and driven end to end — the positional
// pattern is packed against the member's own field layout, so reading a nested
// field back yields the value placed there rather than a mis-concatenated bit
// range.
TEST(TaggedUnionEval, TaggedMemberValueFromStructAssignmentPattern) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { bit [4:0] reg1; bit [4:0] reg2;\n"
      "                          bit [4:0] regd; } add_t;\n"
      "  typedef union tagged { add_t Add; bit [14:0] Jmp; } Instr;\n"
      "  Instr i1;\n"
      "  int result;\n"
      "  initial begin\n"
      "    i1 = tagged Add '{5, 9, 3};\n"
      "    result = i1.Add.reg2;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

// §11.9: a declaration initializer may use the void-member form of a tagged
// expression (no member value primary). It still establishes the active tag, so
// a later read of a different member is inconsistent with that tag and raises a
// run-time error.
TEST(TaggedUnionEval, VoidMemberDeclarationInitializerSetsTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void None; int Some; } Opt;\n"
      "  Opt o = tagged None;\n"
      "  int result;\n"
      "  initial result = o.Some;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
