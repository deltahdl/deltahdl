#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Register a two-member tagged union type "vint" whose members both alias the
// full 32-bit storage, mirroring the void/int VInt example.
StructTypeInfo MakeVIntInfo() {
  StructTypeInfo uinfo;
  uinfo.type_name = "vint";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 32;
  uinfo.fields.push_back({"Invalid", 0, 32, DataTypeKind::kLogic});
  uinfo.fields.push_back({"Valid", 0, 32, DataTypeKind::kLogic});
  return uinfo;
}

// A member may only be read through the name that matches the active tag, so
// reading "Valid" while the tag is "Invalid" must not surrender the stored
// bits as a valid integer; the result carries unknown bits.
TEST(TaggedUnionReadTypeCheck, ReadMemberMismatchedWithTagIsUnknown) {
  SimFixture f;
  f.ctx.RegisterStructType("vint", MakeVIntInfo());
  MakeVar(f, "u", 32, 7);
  f.ctx.SetVariableStructType("u", "vint");
  f.ctx.SetVariableTag("u", "Invalid");

  auto* access = f.arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MakeId(f.arena, "u");
  access->rhs = MakeId(f.arena, "Valid");
  auto result = EvalExpr(access, f.ctx, f.arena);

  ASSERT_NE(result.nwords, 0u);
  EXPECT_NE(result.words[0].bval, 0u);
}

// Reading through the name that matches the active tag returns the stored
// value unchanged.
TEST(TaggedUnionReadTypeCheck, ReadMemberMatchingTagReturnsValue) {
  SimFixture f;
  f.ctx.RegisterStructType("vint", MakeVIntInfo());
  MakeVar(f, "u", 32, 7);
  f.ctx.SetVariableStructType("u", "vint");
  f.ctx.SetVariableTag("u", "Valid");

  auto* access = f.arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MakeId(f.arena, "u");
  access->rhs = MakeId(f.arena, "Valid");
  auto result = EvalExpr(access, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 7u);
}

TEST(TaggedUnionSimulation, ChangeTag) {
  SimFixture f;
  f.ctx.CreateVariable("u", 32);
  f.ctx.SetVariableTag("u", "a");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "a");
  f.ctx.SetVariableTag("u", "b");
  EXPECT_EQ(f.ctx.GetVariableTag("u"), "b");
}

TEST(TaggedUnionSimulation, TaggedAssignment_SetsTagAndValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged Valid 42;\n"
      "    result = u.Valid;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(TaggedUnionSimulation, TaggedAssignment_OverwriteTag) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 10;\n"
      "    u = tagged B 20;\n"
      "    result = u.B;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(TaggedUnionSimulation, VoidMemberTaggedAssignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged Invalid;\n"
      "    u = tagged Valid 99;\n"
      "    result = u.Valid;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 99u);
}

}  // namespace
