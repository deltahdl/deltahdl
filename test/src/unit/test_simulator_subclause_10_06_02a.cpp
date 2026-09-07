#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ForceReleaseSim, VarLvalueForce) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'h00; force x = 8'hFF; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(ForceReleaseExec, ForceNullLhsNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForce;
  stmt->lhs = nullptr;
  stmt->rhs = MakeInt(f.arena, 5);

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(ForceReleaseExec, ReleaseUnknownVarNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRelease;
  stmt->lhs = MakeId(f.arena, "nonexistent");

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(ForceReleaseExec, ReleaseNullLhsNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRelease;
  stmt->lhs = nullptr;

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(ForceReleaseSim, ForcePreventsNonblockingAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x <= 8'd100;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ReforceUpdatesValue) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    force x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 99u);
}

TEST(ForceReleaseSim, ForceOverridesBlockingAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    force x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 99u);
  EXPECT_TRUE(x->is_forced);
}

TEST(ForceReleaseSim, ReleaseVariableHoldsValue) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    release x;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// §10.6.2: once a variable with no continuous assignment or active assign
// procedural continuous assignment is released, it keeps the forced value only
// until the next procedural assignment, which then takes effect normally. The
// released variable therefore resumes accepting ordinary blocking assignments.
TEST(ForceReleaseSim, ReleaseThenProceduralAssignResumes) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    release x;\n"
      "    x = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 77u);
}

TEST(ForceReleaseSim, ForceOverridesAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    assign x = 8'd10;\n"
      "    force x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 99u);
}

TEST(ForceReleaseSim, ForcePreventsBlockingAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x = 8'd100;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForceExpressionRhs) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    force b = a | 8'h0F;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xFFu);
}

TEST(ForceReleaseSim, ReleaseReestablishesAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    assign x = 8'd10;\n"
      "    force x = 8'd99;\n"
      "    release x;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 10u);
}

TEST(ForceReleaseSim, ReleaseReestablishesContinuousAssignment) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] x;\n"
      "  assign x = src;\n"
      "  initial begin\n"
      "    src = 8'd10;\n"
      "    #1;\n"
      "    force x = 8'd99;\n"
      "    #1;\n"
      "    release x;\n"
      "    src = 8'd42;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 42u);
}

TEST(ForceReleaseSim, ForceOnNetOverridesContinuousDriver) {
  SimFixture f;
  auto* w = RunAndFindVar(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  assign w = 8'd10;\n"
      "  initial begin\n"
      "    #1;\n"
      "    force w = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->is_forced);
  EXPECT_EQ(w->value.ToUint64(), 99u);
}

TEST(ForceReleaseSim, ReleaseOnNetUsesDriverValue) {
  SimFixture f;
  auto* w = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire [7:0] w;\n"
      "  assign w = src;\n"
      "  initial begin\n"
      "    src = 8'd10;\n"
      "    #1;\n"
      "    force w = 8'd99;\n"
      "    #1;\n"
      "    release w;\n"
      "    src = 8'd55;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_FALSE(w->is_forced);
  EXPECT_EQ(w->value.ToUint64(), 55u);
}

// A force on a net overrides every kind of driver until the net is released,
// not just continuous assignments. Here a primitive AND gate drives w to 1,
// yet the force holds w at 0 while it is in effect.
TEST(ForceReleaseSim, ForceOverridesGateOutputDriver) {
  SimFixture f;
  auto* w = RunAndFindVar(
      "module t;\n"
      "  logic a, b;\n"
      "  wire w;\n"
      "  and g(w, a, b);\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    #1;\n"
      "    force w = 1'b0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->is_forced);
  EXPECT_EQ(w->value.ToUint64(), 0u);
}

// Releasing a net makes it take the value its drivers determine right away.
// After release the AND gate (1 & 1) drives w back to 1, displacing the
// forced 0.
TEST(ForceReleaseSim, ReleaseNetReturnsToGateOutputValue) {
  SimFixture f;
  auto* w = RunAndFindVar(
      "module t;\n"
      "  logic a, b;\n"
      "  wire w;\n"
      "  and g(w, a, b);\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    #1;\n"
      "    force w = 1'b0;\n"
      "    #1;\n"
      "    release w;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_FALSE(w->is_forced);
  EXPECT_EQ(w->value.ToUint64(), 1u);
}

// §10.6.2 names module outputs among the drivers a force overrides, alongside
// gate outputs and continuous assignments. Here child instance u drives w to 10
// through its output port; the force pins w to 99 while in effect, and after
// the release w immediately returns to the value its port driver determines.
TEST(ForceReleaseSim, ForceOverridesModuleOutputDriver) {
  SimFixture f;
  auto* w = RunAndFindVar(
      "module drv(output logic [7:0] o);\n"
      "  assign o = 8'd10;\n"
      "endmodule\n"
      "module t;\n"
      "  wire [7:0] w;\n"
      "  drv u(w);\n"
      "  initial begin\n"
      "    #1;\n"
      "    force w = 8'd99;\n"
      "    #1;\n"
      "    release w;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_FALSE(w->is_forced);
  EXPECT_EQ(w->value.ToUint64(), 10u);
}

// §10.6.2: "A force procedural statement on a net shall override all drivers of
// the net -- gate outputs, module outputs, and continuous assignments -- until
// a release procedural statement is executed on the net." Overridden drivers
// are not driving, so the strength the net reports is the force's and not
// theirs. §10.6 gives force no drive_strength syntax, so the strength is the
// (strong1, strong0) §10.3.4 defaults to, which §21.2.1.4 renders St1.
//
// A pull1 continuous assignment is what the force overrides here: driver and
// force disagree about the level while agreeing about the value, so a net
// reporting Pu1 is reporting the driver it is not carrying.
TEST(ForceReleaseSim,
     ForcedNetReportsTheForcesStrengthNotTheDriversItOverrode) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull0, pull1) w = 1'b1;\n"
      "  initial begin\n"
      "    #1 force w = 1'b1;\n"
      "    #1 $display(\"%v\", w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("St1"), std::string::npos) << out;
  EXPECT_EQ(out.find("Pu1"), std::string::npos) << out;
}

// §10.6.2: the force is the net's source from the moment it executes, so a net
// forced before anything drove it carries a strength too. Reporting the
// strength only when a driver update happens to re-resolve the net leaves this
// one at high impedance while it carries a value.
TEST(ForceReleaseSim, NetForcedWithNoDriverStillReportsAStrength) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    force w = 1'b0;\n"
      "    #1 $display(\"%v\", w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("St0"), std::string::npos) << out;
  EXPECT_EQ(out.find("HiZ"), std::string::npos) << out;
}

// §10.6.2: "When released, the net shall immediately be assigned the value
// determined by the drivers of the net" -- and the strength with it, the
// drivers being what drives again. Without this case, reporting the force's
// strength for good satisfies the two above.
TEST(ForceReleaseSim, ReleasedNetReportsItsDriversStrengthAgain) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull0, pull1) w = 1'b1;\n"
      "  initial begin\n"
      "    #1 force w = 1'b1;\n"
      "    #1 release w;\n"
      "    #1 $display(\"%v\", w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("Pu1"), std::string::npos) << out;
}

}  // namespace
