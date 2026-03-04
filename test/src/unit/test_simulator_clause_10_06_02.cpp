#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_force_target.h"
#include "helpers_stmt_exec.h"
#include "helpers_switch_network.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimA85, VarLvalueForce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'h00; force x = 8'hFF; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(ForceRelease, LegalTargetSingularVariable) {
  ForceInfo info{ForceTarget::kSingularVariable};
  EXPECT_TRUE(ValidateForceTarget(info));
}

TEST(ForceRelease, LegalTargetConstBitSelectNet) {
  ForceInfo info{ForceTarget::kConstBitSelectNet};
  EXPECT_TRUE(ValidateForceTarget(info));
}

TEST(ForceRelease, LegalTargetConstPartSelectNet) {
  ForceInfo info{ForceTarget::kConstPartSelectNet};
  EXPECT_TRUE(ValidateForceTarget(info));
}

TEST(ForceRelease, IllegalUserDefinedNettypePartSelect) {
  ForceInfo info{ForceTarget::kUserDefinedNettypePartSelect};
  EXPECT_FALSE(ValidateForceTarget(info));
}

void ForceVariable(Variable& var, const Logic4Vec& value) { var.value = value; }

TEST(ForceRelease, ForceVariableOverridesValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 1, 1);
  EXPECT_EQ(ValOf(*var), kVal1);

  ForceVariable(*var, MakeLogic4VecVal(arena, 1, 0));
  EXPECT_EQ(ValOf(*var), kVal0);
}

void ReleaseVariable(Variable& var, bool has_continuous_driver,
                     const Logic4Vec* continuous_value, Arena& arena) {
  (void)arena;
  if (has_continuous_driver && continuous_value) {
    var.value = *continuous_value;
  }
}

TEST(ForceRelease, ReleaseUndrivenVariableHoldsValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 1, 0);

  ForceVariable(*var, MakeLogic4VecVal(arena, 1, 1));
  EXPECT_EQ(ValOf(*var), kVal1);

  ReleaseVariable(*var, false, nullptr, arena);

  EXPECT_EQ(ValOf(*var), kVal1);
}

TEST(ForceRelease, ReleaseContinuouslyDrivenVariableReestablishes) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 1, 0);

  Logic4Vec continuous_val = MakeLogic4VecVal(arena, 1, 0);

  ForceVariable(*var, MakeLogic4VecVal(arena, 1, 1));
  EXPECT_EQ(ValOf(*var), kVal1);

  ReleaseVariable(*var, true, &continuous_val, arena);

  EXPECT_EQ(ValOf(*var), kVal0);
}

void ForceNet(Net& net, const Logic4Vec& value, Arena& arena) {
  (void)arena;
  net.resolved->value = value;
}

TEST(ForceRelease, ForceNetOverridesAllDrivers) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);

  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));

  ForceNet(net, MakeLogic4VecVal(arena, 1, 1), arena);
  EXPECT_EQ(ValOf(*var), kVal1);
}

void ReleaseNet(Net& net, Arena& arena) {
  (void)arena;
  if (!net.drivers.empty()) {
    net.resolved->value = net.drivers[0];
  } else {
    for (uint32_t i = 0; i < net.resolved->value.nwords; ++i) {
      net.resolved->value.words[i].aval = 1;
      net.resolved->value.words[i].bval = 1;
    }
  }
}

TEST(ForceRelease, ReleaseNetImmediatelyRestoresDriverValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);

  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));

  ForceNet(net, MakeLogic4VecVal(arena, 1, 1), arena);
  EXPECT_EQ(ValOf(*var), kVal1);

  ReleaseNet(net, arena);

  EXPECT_EQ(ValOf(*var), kVal0);
}

struct TwoNets {
  Arena arena;
  Variable* vd = nullptr;
  Variable* ve = nullptr;
  Net net_d;
  Net net_e;
};

static TwoNets MakeTwoWireNets() {
  TwoNets tn;
  tn.vd = tn.arena.Create<Variable>();
  tn.vd->value = MakeLogic4Vec(tn.arena, 1);
  tn.ve = tn.arena.Create<Variable>();
  tn.ve->value = MakeLogic4Vec(tn.arena, 1);
  tn.net_d.type = NetType::kWire;
  tn.net_d.resolved = tn.vd;
  tn.net_d.drivers.push_back(MakeLogic4VecVal(tn.arena, 1, 0));
  tn.net_e.type = NetType::kWire;
  tn.net_e.resolved = tn.ve;
  tn.net_e.drivers.push_back(MakeLogic4VecVal(tn.arena, 1, 0));
  return tn;
}

TEST(ForceRelease, NormativeExampleForceAndRelease_InitialState) {
  auto tn = MakeTwoWireNets();

  ReleaseNet(tn.net_d, tn.arena);
  ReleaseNet(tn.net_e, tn.arena);
  EXPECT_EQ(ValOf(*tn.vd), kVal0);
  EXPECT_EQ(ValOf(*tn.ve), kVal0);
}

TEST(ForceRelease, NormativeExampleForceAndRelease_ForceAndRelease) {
  auto tn = MakeTwoWireNets();

  ForceNet(tn.net_d, MakeLogic4VecVal(tn.arena, 1, 1), tn.arena);
  ForceNet(tn.net_e, MakeLogic4VecVal(tn.arena, 1, 1), tn.arena);
  EXPECT_EQ(ValOf(*tn.vd), kVal1);
  EXPECT_EQ(ValOf(*tn.ve), kVal1);

  ReleaseNet(tn.net_d, tn.arena);
  ReleaseNet(tn.net_e, tn.arena);
  EXPECT_EQ(ValOf(*tn.vd), kVal0);
  EXPECT_EQ(ValOf(*tn.ve), kVal0);
}

TEST(StmtExec, ForceOverridesValue) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("x", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForce;
  stmt->lhs = MakeId(f.arena, "x");
  stmt->rhs = MakeInt(f.arena, 99);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_TRUE(var->is_forced);
  EXPECT_EQ(var->forced_value.ToUint64(), 99u);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(StmtExec, ForceNullLhsNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForce;
  stmt->lhs = nullptr;
  stmt->rhs = MakeInt(f.arena, 5);

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(StmtExec, ReleaseClearsForce) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("y", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);
  var->is_forced = true;
  var->forced_value = MakeLogic4VecVal(f.arena, 32, 42);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRelease;
  stmt->lhs = MakeId(f.arena, "y");

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);
}

TEST(StmtExec, ReleaseUnknownVarNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRelease;
  stmt->lhs = MakeId(f.arena, "nonexistent");

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(StmtExec, ForcePreventsNormalAssign) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("fv", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* force_stmt = f.arena.Create<Stmt>();
  force_stmt->kind = StmtKind::kForce;
  force_stmt->lhs = MakeId(f.arena, "fv");
  force_stmt->rhs = MakeInt(f.arena, 50);
  RunStmt(force_stmt, f.ctx, f.arena);

  auto* assign_stmt = MakeBlockAssign(f.arena, "fv", 100);
  RunStmt(assign_stmt, f.ctx, f.arena);

  EXPECT_TRUE(var->is_forced);

  EXPECT_EQ(var->forced_value.ToUint64(), 50u);
}

TEST(StmtExec, ForceReleaseThenAssign) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("fra", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* force_stmt = f.arena.Create<Stmt>();
  force_stmt->kind = StmtKind::kForce;
  force_stmt->lhs = MakeId(f.arena, "fra");
  force_stmt->rhs = MakeInt(f.arena, 50);
  RunStmt(force_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 50u);
  EXPECT_TRUE(var->is_forced);

  auto* release_stmt = f.arena.Create<Stmt>();
  release_stmt->kind = StmtKind::kRelease;
  release_stmt->lhs = MakeId(f.arena, "fra");
  RunStmt(release_stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);

  auto* assign_stmt = MakeBlockAssign(f.arena, "fra", 75);
  RunStmt(assign_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 75u);
}

}  // namespace
