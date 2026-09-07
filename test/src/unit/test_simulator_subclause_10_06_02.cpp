#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "helpers_switch_network.h"
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

// §10.6.2: "A force statement to a variable shall override a procedural
// assignment, continuous assignment or an assign procedural continuous
// assignment to the variable until a release procedural statement is executed
// on the variable." §11.4.1 states a compound assignment as one of those
// assignments -- "an assignment operator is semantically equivalent to a
// blocking assignment" -- and §10.4 puts a blocking assignment written in an
// initial block among the procedural assignments, so `x += 8'd10;` is the same
// statement ForcePreventsBlockingAssign above writes and the force declines it
// the same way.
//
// A compound operator is the one form that reaches WriteVar, and WriteVar was
// the only writer on the blocking-assignment path that consulted the flag
// nowhere, so this read 60 -- the forced 50 with the 10 added to it -- where
// the plain `x = 8'd100;` above already read 50. No other case in this file
// reaches that writer.
TEST(ForceReleaseSim, ForcePreventsACompoundAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x += 8'd10;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// §11.4.2 states the increment and decrement operators as blocking assignments
// -- "These increment and decrement assignment operators behave as blocking
// assignments" -- so §10.6.2 overrides `x++` exactly as it overrides the
// `x = 8'd100;` of ForcePreventsBlockingAssign and the `x += 8'd10;` of
// ForcePreventsACompoundAssign above. A bare `x++;` is an expression statement
// naming no subroutine, so ExecInlineTaskCall declines it and hands it to
// EvalExpr; the increment therefore happens in the expression evaluator rather
// than on any statement-assignment path.
//
// That is why this case failed while the two above passed. EvalIncDec stores
// into var->value itself instead of calling WriteVar, so the guard #3506 put
// in WriteVar sat on a path this one never takes: the increment read the
// forced 50, added 1 and stored 51.
//
// Only the write is declined -- the operator still yields the value it
// computed -- but a postfix `++` yields what the target held beforehand, which
// is the forced 50 whether or not the write lands. Nothing here can read that
// half of the rule; the case below is what does.
TEST(ForceReleaseSim, ForcePreventsAnIncrement) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x++;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The increment written where its value is read. EvalIncDec is one function
// for all four spellings, so a decrement and a postfix form cannot fail while
// ForcePreventsAnIncrement passes; what they cannot say is whether the decline
// stopped at the write. §11.4.2 states the operator as a blocking assignment,
// which §10.6.2 overrides, and states nothing about the value it yields, so a
// prefix increment still reads 51 while the target it declined to write stays
// at the forced 50. A decline written as an early return from EvalIncDec would
// hand back the operand unchanged and leave y at 50.
TEST(ForceReleaseSim, ForcePreventsAnIncrementWithoutChangingWhatItYields) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    y = (++x);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 50u);

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 51u);
}

// The compound operator written as an expression rather than as a statement.
// §11.4.1 makes the two spellings one assignment, so §10.6.2 declines both;
// but the expression form reaches neither WriteVar nor the read-modify-write
// the statement form performs. EvalCompoundAssign stores into var->value
// itself, so x read 60 here -- the forced 50 with the 10 added to it -- after
// ForcePreventsACompoundAssign above had already been made to read 50.
//
// y is what says the decline is confined to the write. §11.3.6 has an
// assignment expression "evaluates the right-hand side, casts the right-hand
// side to the left-hand data type, stacks it, updates the left-hand side, and
// returns the stacked value": the value is stacked before the update, so what
// comes back is the value the operator computed and not a re-read of the
// target. The addition produces 60 whichever way the update goes, so y takes
// 60 while x stays at 50. A decline written as an early return from
// EvalCompoundAssign, or as returning what the forced target still holds,
// would leave y at 50 and satisfy the assertions on x alone.
//
// LvalueSim.CompoundAssignExpressionYieldsTheTargetsDataType in
// test_simulator_subclause_11_04_01.cpp reads the rest of the same sentence,
// that "the data type of the value that is returned is the data type of the
// left-hand side" -- which is what sizes this 60 at x's eight bits rather than
// at the literal's.
TEST(ForceReleaseSim, ForcePreventsACompoundAssignWrittenAsAnExpression) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    y = (x += 8'd10);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 50u);

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 60u);
}

// §10.6.2: "A force statement to a variable shall override a procedural
// assignment, continuous assignment or an assign procedural continuous
// assignment to the variable until a release procedural statement is executed
// on the variable." §10.4 puts a blocking assignment written in an initial
// block among those procedural assignments, and naming a bit-select as the
// target does not take the statement out of that class -- the clause's own "It
// shall not be a bit-select or a part-select of a variable" restricts what may
// be forced, not what a force overrides.
//
// This is ForcePreventsBlockingAssign with the target indexed, and it is the
// case that claims WriteBitSelect. Every whole-variable writer declines --
// WriteVar, AssignToScalarLhs, PerformBlockingAssign -- but a select target
// reaches none of them. TryResolveArrayElement asks for an element variable
// named `x[3]`, and CreateArrayElements makes those only for an unpacked
// declaration, so a packed `logic [7:0] x` has none; ResolveLhsVariable then
// walks the select down to its base and TrySelectBlockingAssign hands the whole
// variable to WriteBitSelect, which consulted the flag nowhere. The forced 50
// is 8'b0011_0010, so depositing a 1 in bit 3 read 58.
TEST(ForceReleaseSim, ForcePreventsABitSelectAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The same rule stated against a part-select. WriteBitSelect holds two deposits
// and the presence of an index_end is what picks between them: a bit-select
// clears and sets the one bit in place and returns, while a part-select
// resolves the window the select names and hands it to WritePartSelect, which
// the bit-select case above never enters. A decline written into the
// bit-select arm rather than at the top of the writer would leave this form
// overriding the force.
//
// The forced 50 is 8'b0011_0010, whose low nibble is 4'h2, so writing 4'hF over
// x[3:0] read 63 where §10.6.2 has the write not land at all.
TEST(ForceReleaseSim, ForcePreventsAPartSelectAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3:0] = 4'hF;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The select form of §11.4.1's compound operator, which is a second route into
// the same writer rather than a second writer. ApplyCompoundAssignOp's select
// arm asks TryResolveArrayElement for an element variable first and, a packed
// vector having none, falls through to the branch that reads the target,
// computes, and writes the result back through TrySelectBlockingAssign. It
// never reaches AssignToScalarLhs, which is the arm that would have declined on
// its own, so this is the route that would silently escape a decline applied at
// only one of WriteBitSelect's call sites.
//
// Traced for `logic [7:0] x`: x[3] of the forced 8'b0011_0010 reads 0, the
// addition makes 1, and WriteBitSelect deposited that in bit 3 for 58 -- the
// same answer the plain bit-select assignment above gave, arrived at by a
// different path, which is what makes the route and not the value the thing
// this case claims.
TEST(ForceReleaseSim, ForcePreventsABitSelectCompoundAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3] += 1;\n"
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

// §10.4 puts procedural assignments "within procedures such as always, initial,
// task, and function", so the assignment a force overrides is the same
// statement wherever it is written.
//
// A task called with parentheses runs its body on the ordinary statement
// executor: SetupTaskCall claims a kTaskDecl and ExecInlineTaskCall walks the
// body through ExecStmt, reaching the same AssignToScalarLhs that
// ForcePreventsBlockingAssign above exercises. So this case reads the rule
// through a task call rather than through the subroutine-body executor, and the
// function case below is what claims that executor -- a void function called
// with parentheses is declined by SetupTaskCall and reaches ExecFunctionBody
// instead.
TEST(ForceReleaseSim, ForcePreventsATaskBodyAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task poke();\n"
      "    x = 8'd100;\n"
      "  endtask\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The subroutine-body executor itself, which consulted the flag nowhere, so an
// assignment written here overwrote a forced variable where the same statement
// in an initial block or in a task did not.
TEST(ForceReleaseSim, ForcePreventsAFunctionBodyAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void poke();\n"
      "    x = 8'd100;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The same compound assignment written in a function body. This is not a second
// writer: #3500 routed the subroutine-body executor's `lhs op= rhs` to
// ApplyCompoundAssignOp, the single read-modify-write the ordinary statement
// executor performs, so this case and ForcePreventsACompoundAssign above now
// reach WriteVar by one route rather than two. What it claims is that the rule
// holds for the subroutine route as well, §10.4 putting procedural assignments
// "within procedures such as always, initial, task, and function".
//
// Before #3500 this case failed for a different reason than the initial-block
// one: the statement's right-hand side is itself the compound operator, so
// evaluating it reached EvalCompoundAssign, which wrote x before
// ExecFuncIdentifierAssign's own is_forced check could decline the write it was
// handed. Either way the answer was 60 and §10.6.2 says 50.
TEST(ForceReleaseSim, ForcePreventsACompoundAssignInAFunctionBody) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void poke();\n"
      "    x += 8'd10;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The select target written inside a subroutine body, which is the last of the
// six routes into WriteBitSelect. The subroutine-body executor is its own
// execution of every statement form, and its select arm ExecFuncSelectAssign
// calls TrySelectBlockingAssign directly rather than going through the
// statement executor's arms.
//
// A function is what reaches that arm, not a task. SetupTaskCall claims a
// kTaskDecl and ExecInlineTaskCall then walks the body through the ordinary
// ExecStmt, so `x[3] = 1'b1;` written in a `task poke;` retraces
// ForcePreventsABitSelectAssign's route instead of claiming a new one; a void
// function called with parentheses is declined by SetupTaskCall and reaches
// ExecFunctionBody, exactly as ForcePreventsAFunctionBodyAssign above records.
// §10.4 puts procedural assignments "within procedures such as always, initial,
// task, and function", so this is the same statement wherever it is written,
// and it read 58 here as well.
TEST(ForceReleaseSim, ForcePreventsABitSelectAssignInAFunctionBody) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void poke();\n"
      "    x[3] = 1'b1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

// The other half of §10.6.2: the override lasts "until a release procedural
// statement is executed on the variable", and a released variable "shall
// maintain its current value until the next procedural assignment to the
// variable is executed". That next assignment is the one inside the task here,
// so this is what says the decline above is bounded by the release rather than
// standing for the rest of the run.
TEST(ForceReleaseSim, ReleaseThenATaskBodyAssignResumes) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task poke();\n"
      "    x = 8'd77;\n"
      "  endtask\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "    release x;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 77u);
}

// The compound operator's half of the other rule in §10.6.2: the override lasts
// "until a release procedural statement is executed on the variable", and a
// released variable "shall maintain its current value until the next procedural
// assignment to the variable is executed". Here that next assignment is itself
// a compound one, so the released 50 becomes 77 rather than staying at 50.
//
// ForcePreventsACompoundAssign and ForcePreventsACompoundAssignInAFunctionBody
// are the only other cases in this file that reach WriteVar, and both expect it
// to write nothing; a WriteVar that dropped every write would satisfy them.
// This is what says the new decline is the force's and is bounded by the
// release -- and the first `x += 8'd10;` here, which leaves x at 50 and not 60,
// is what makes 77 the answer rather than 87.
TEST(ForceReleaseSim, ReleaseThenACompoundAssignResumes) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x += 8'd10;\n"
      "    release x;\n"
      "    x += 8'd27;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 77u);
}

// The select form's half of the other rule in §10.6.2: the override lasts
// "until a release procedural statement is executed on the variable", and a
// released variable "shall maintain its current value until the next procedural
// assignment to the variable is executed". Every select case above expects
// WriteBitSelect to write nothing, so a decline that never lifted would satisfy
// all four of them; this is what says the decline is the force's and is bounded
// by the release.
//
// The forced 50 is 8'b0011_0010, in which bit 3 and bit 0 are both clear, so
// the two writes separate three outcomes. 50 is the decline never lifting and
// neither write landing. 59 is the pre-release `x[3] = 1'b1;` having wrongly
// landed alongside the post-release one, 50 | 8 | 1. 51 is what §10.6.2 asks
// for: the write before the release declined and only the write after it
// landing. (A fourth reading, 58, would be the pre-release write landing and
// the post-release one not, which is the rule inverted.)
TEST(ForceReleaseSim, ReleaseThenABitSelectAssignResumes) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3] = 1'b1;\n"
      "    release x;\n"
      "    x[0] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 51u);
}

}  // namespace
