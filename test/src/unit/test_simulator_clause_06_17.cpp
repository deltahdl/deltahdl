#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(Lowerer, EventVariableCreated) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("ev");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_event);
}

TEST(Simulator, EventTriggeredStatePersistsInTimestep) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  initial ->ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_FALSE(f.ctx.IsEventTriggered("ev"));

  f.ctx.SetEventTriggered("ev");
  EXPECT_TRUE(f.ctx.IsEventTriggered("ev"));
}

TEST(Simulator, EventAssignNullSetsNullFlag) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("ev");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->is_null_event);

  f.ctx.NullifyEventVariable("ev");
  EXPECT_TRUE(var->is_null_event);
}

TEST(Simulator, EventToEventAlias) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  event b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  f.ctx.AliasVariable("b", "a");
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  EXPECT_EQ(va, vb);
}

TEST(Simulator, EventInitializedWithNullFlag) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev = null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("ev");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_null_event);
}

TEST(Simulator, EventDefaultInitYieldsDistinctSyncObjects) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  event b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_NE(va, vb);
  EXPECT_FALSE(va->is_null_event);
  EXPECT_FALSE(vb->is_null_event);
}

TEST(Simulator, EventAliasInitializerSharesSyncObject) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event done;\n"
      "  event done_too = done;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* done = f.ctx.FindVariable("done");
  auto* done_too = f.ctx.FindVariable("done_too");
  ASSERT_NE(done, nullptr);
  ASSERT_NE(done_too, nullptr);
  EXPECT_EQ(done, done_too);
}

TEST(Simulator, EventBlockingAssignToOtherEventAliases) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  event b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  ASSERT_NE(f.ctx.FindVariable("a"), f.ctx.FindVariable("b"));

  auto* stmt = MakeAssign(f.arena, "b", MakeId(f.arena, "a"));
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("a"), f.ctx.FindVariable("b"));
}

TEST(Simulator, EventBlockingAssignNullBreaksAssociation) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  ASSERT_FALSE(f.ctx.FindVariable("ev")->is_null_event);

  auto* stmt = MakeAssign(f.arena, "ev", MakeId(f.arena, "null"));
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  auto* after = f.ctx.FindVariable("ev");
  ASSERT_NE(after, nullptr);
  EXPECT_TRUE(after->is_null_event);
}

TEST(Simulator, EventEqualityComparesSyncObjectIdentity) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  event b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* eq = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "a"),
                        MakeId(f.arena, "b"));
  EXPECT_EQ(EvalExpr(eq, f.ctx, f.arena).ToUint64(), 0u);

  f.ctx.AliasVariable("b", "a");
  EXPECT_EQ(EvalExpr(eq, f.ctx, f.arena).ToUint64(), 1u);
}

TEST(Simulator, EventNullComparisonReflectsBrokenAssociation) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* eq_null = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "ev"),
                             MakeId(f.arena, "null"));
  EXPECT_EQ(EvalExpr(eq_null, f.ctx, f.arena).ToUint64(), 0u);

  f.ctx.NullifyEventVariable("ev");
  EXPECT_EQ(EvalExpr(eq_null, f.ctx, f.arena).ToUint64(), 1u);
}

TEST(Simulator, EventSelfEqualityIsTrue) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* eq_self = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "ev"),
                             MakeId(f.arena, "ev"));
  EXPECT_EQ(EvalExpr(eq_self, f.ctx, f.arena).ToUint64(), 1u);
}

TEST(Simulator, EventInequalityComparesSyncObjectIdentity) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  event b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* ne = MakeBinary(f.arena, TokenKind::kBangEq, MakeId(f.arena, "a"),
                        MakeId(f.arena, "b"));
  EXPECT_EQ(EvalExpr(ne, f.ctx, f.arena).ToUint64(), 1u);

  f.ctx.AliasVariable("b", "a");
  EXPECT_EQ(EvalExpr(ne, f.ctx, f.arena).ToUint64(), 0u);
}

TEST(Simulator, EventTriggeredStatePropagatesThroughAlias) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  event b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_FALSE(f.ctx.IsEventTriggered("a"));
  EXPECT_FALSE(f.ctx.IsEventTriggered("b"));

  f.ctx.SetEventTriggered("a");
  EXPECT_TRUE(f.ctx.IsEventTriggered("a"));
  EXPECT_TRUE(f.ctx.IsEventTriggered("b"));
}

TEST(Simulator, IndependentEventsHaveIndependentTriggeredState) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  event b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  f.ctx.SetEventTriggered("a");
  EXPECT_TRUE(f.ctx.IsEventTriggered("a"));
  EXPECT_FALSE(f.ctx.IsEventTriggered("b"));
}

TEST(Simulator, NullifyOnAliasOnlyBreaksAssignedVariable) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  event b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  ASSERT_EQ(f.ctx.FindVariable("a"), f.ctx.FindVariable("b"));

  auto* stmt = MakeAssign(f.arena, "b", MakeId(f.arena, "null"));
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  auto* after_a = f.ctx.FindVariable("a");
  auto* after_b = f.ctx.FindVariable("b");
  ASSERT_NE(after_a, nullptr);
  ASSERT_NE(after_b, nullptr);
  EXPECT_NE(after_a, after_b);
  EXPECT_FALSE(after_a->is_null_event);
  EXPECT_TRUE(after_b->is_null_event);
}

}  // namespace
