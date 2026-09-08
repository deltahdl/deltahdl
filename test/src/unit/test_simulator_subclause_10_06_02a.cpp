#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
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

// §10.6.2: "The left-hand side of the assignment can be a reference to a
// singular variable, a net, a constant bit-select of a vector net, a constant
// part-select of a vector net, or a concatenation of these." A concatenation of
// two whole variables is one of the forms that sentence names, so the force
// takes effect on both of its elements; §11.4.12 -- "The concatenation is
// treated as a packed vector of bits" -- is what says how one right-hand value
// reaches two targets, each element taking the bits its own width claims with
// the leftmost taking the most significant ones. With `logic [7:0] a, b;` and
// 16'h1234 that is 8'h12 for a and 8'h34 for b.
//
// The wrong answer was that nothing happened at all, and silently: the force
// executor resolved its one target through ResolveLhsVariable, which answers
// null for a concatenation, and returned kDone having marked nothing, written
// nothing and reported nothing. Both elements start at sentinels no expected
// value can be, so a force that writes nothing cannot pass for one that wrote
// the right answer.
TEST(ForceReleaseSim, ForceOfAConcatenationGivesEachElementItsSlice) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hA1;\n"
      "    b = 8'hB2;\n"
      "    force {a, b} = 16'h1234;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_TRUE(a->is_forced);
  EXPECT_TRUE(b->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 0x12u);
  EXPECT_EQ(b->value.ToUint64(), 0x34u);
}

// §10.6.2: "A force statement to a variable shall override a procedural
// assignment ... to the variable until a release procedural statement is
// executed on the variable." That override is what makes the statement above a
// force rather than a one-off write of a slice, and it is carried by the
// is_forced flag the existing writers consult, so this case says the flag the
// concatenation arm sets is the one they already read. Without it, an arm that
// deposited each slice and marked nothing would satisfy the case above.
//
// The wrong answer was silence in both halves: the force marked neither element
// and the later `a = 8'd7;` therefore landed, leaving a at 7 rather than at the
// slice the force gave it.
TEST(ForceReleaseSim, ForceOfAConcatenationOverridesALaterElementAssign) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hA1;\n"
      "    b = 8'hB2;\n"
      "    force {a, b} = 16'h1234;\n"
      "    a = 8'd7;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_TRUE(a->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 0x12u);
  EXPECT_EQ(b->value.ToUint64(), 0x34u);
}

// §10.6.2 bounds the override by the release -- once released, a variable
// "shall maintain its current value until the next procedural assignment to the
// variable is executed" -- and the release names the same concatenation the
// force did, so it has to reach every element the force marked. This is the
// companion the file writes for every other form (ReleaseVariableHoldsValue,
// ReleaseThenProceduralAssignResumes), and it is what keeps the concatenation
// arm from installing a force no release can lift.
//
// The wrong answer was that neither statement did anything: release resolved
// its target through the same ResolveLhsVariable and returned having cleared
// nothing. The assignments after the release are what read the flag back --
// each element takes its ordinary procedural assignment again, which a still
// forced element would decline.
TEST(ForceReleaseSim, ReleaseOfAConcatenationLiftsTheForceOnEachElement) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hA1;\n"
      "    b = 8'hB2;\n"
      "    force {a, b} = 16'h1234;\n"
      "    release {a, b};\n"
      "    a = 8'd7;\n"
      "    b = 8'd9;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_FALSE(a->is_forced);
  EXPECT_FALSE(b->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 7u);
  EXPECT_EQ(b->value.ToUint64(), 9u);
}

// §10.6.2 admits "a constant bit-select of a vector net" among the elements a
// force's concatenation may mix, and the elaborator case
// ForceConcatWithNetBitSelectElaborates accepts exactly `force {w, bus[3]} =
// 2'b11;` on `wire w; wire [7:0] bus;`, so the simulator owes that spelling an
// answer. The element's window is the point: bus[3] claims one bit of the
// right-hand value and one bit of bus, and the seven bits of bus its select
// does not name keep the value its driver gave them, the way §11.4.1's
// distribution leaves the rest of a select element's variable standing. Driving
// bus with 8'h55 makes bit 3 the only zero among a distinctive pattern, so
// 8'h5D is reachable only by writing that one bit.
//
// The wrong answer was that nothing happened: neither element was written, w
// stayed at the 0 its driver gave it and bus stayed at 8'h55. A whole-target
// write is the other wrong answer this case names -- it would put the 2-bit
// right-hand value over all of bus.
//
// bus is left marked forced in its entirety, which is #3512 and not this case's
// claim; nothing here reads bus's flag or writes its other bits.
TEST(ForceReleaseSim, ForceOfAConcatenationWritesOnlyTheNetBitItsSelectNames) {
  SimFixture f;
  auto* w = RunAndFindVar(
      "module t;\n"
      "  wire w;\n"
      "  wire [7:0] bus;\n"
      "  assign w = 1'b0;\n"
      "  assign bus = 8'h55;\n"
      "  initial begin\n"
      "    #1;\n"
      "    force {w, bus[3]} = 2'b11;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(w, nullptr);
  auto* bus = f.ctx.FindVariable("bus");
  ASSERT_NE(bus, nullptr);
  EXPECT_TRUE(w->is_forced);
  EXPECT_EQ(w->value.ToUint64(), 1u);
  EXPECT_EQ(bus->value.ToUint64(), 0x5Du);
}

// §10.6.2: "Releasing a variable that is driven by a continuous assignment or
// currently has an active assign procedural continuous assignment shall
// reestablish that assignment and schedule a reevaluation in the continuous
// assignment's scheduling region." That is ReleaseReestablishesAssign reached
// through a concatenation, and it is the case the reestablishment path can fail
// on its own: the release writes the assign's right-hand value again, long
// after the force looked correct, so an element carrying no window of its own
// quietly takes the whole 16-bit value there. The value the reestablished
// assign leaves is the same distribution the assign itself made -- 8'h12 for a
// and 8'h34 for b -- and an a reading 8'h34 is the whole value truncated into
// it rather than its slice.
//
// The wrong answer today is that all three statements are no-ops and a and b
// stand at their sentinels. What the flag reads after a reestablished assign is
// ReleaseReestablishesAssign's subject, not this one's, so nothing here asserts
// on it.
TEST(ForceReleaseSim, ReleaseOfAConcatenationReestablishesTheAssignPerElement) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hA1;\n"
      "    b = 8'hB2;\n"
      "    assign {a, b} = 16'h1234;\n"
      "    force {a, b} = 16'h5678;\n"
      "    release {a, b};\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0x12u);
  EXPECT_EQ(b->value.ToUint64(), 0x34u);
}

// §11.5.1's report for a select written with a zero width is owed by every
// writer that reaches such a select, and §10.6.1 and §10.6.2 send `assign`,
// `force`, `release` and `deassign` over a concatenation target through a walk
// of their own: WalkConcatLhsElements in statement_assign_decl.cpp, which
// carried the same `if (w == 0) continue;` arm the blocking unpacker carried
// and the same silence with it. The blocking assignment's reading of the rule
// is ConcatenationSim.LhsConcatZeroWidthPartSelectElementNames11_5_1 in
// test_simulator_subclause_11_04_12.cpp; this is the force's, and the two are
// separate functions in separate files, so either can be corrected while the
// other stays silent.
//
// The select is on a net because §10.6.2 admits "a constant bit-select of a
// vector net, a constant part-select of a vector net, or a concatenation of
// these" and nothing wider: CheckForceLhsOperand rejects a select of a variable
// in a force lvalue outright, which is why `bus` is a wire here as it is in
// ForceOfAConcatenationWritesOnlyTheNetBitItsSelectNames above.
//
// The width is a variable because a folded constant zero never reaches the
// simulator at all -- CheckIndexedPartSelectWidthNode rejects it during
// elaboration -- and that leaves the elaborator reporting the variable width as
// the non-constant expression it is, "indexed part-select width must be a
// constant expression", at this same line 10 and under this same §11.5.1. The
// line and the subclause therefore separate nothing, and the message is what
// names the report this case is about.
//
// The values say the force landed rather than the statement being dropped
// whole. The zero-width element claims none of the right-hand value, so `w` is
// the whole of a one-bit concatenation and takes the 1 of 2'b01 against the 0
// its own continuous assignment drives, and `bus`, which the walk passes over,
// keeps the 8'h55 its driver gave it.
TEST(ForceReleaseSim, ForceOfAConcatenationZeroWidthPartSelectNames11_5_1) {
  SimFixture f;
  auto* w = RunAndFindVar(
      "module t;\n"
      "  wire w;\n"
      "  wire [7:0] bus;\n"
      "  logic [3:0] wid;\n"
      "  assign w = 1'b0;\n"
      "  assign bus = 8'h55;\n"
      "  initial begin\n"
      "    wid = 4'd0;\n"
      "    #1;\n"
      "    force {w, bus[3 +: wid]} = 2'b01;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "zero-width part-select is not allowed", 10,
                            "11.5.1"));
  EXPECT_TRUE(w->is_forced);
  EXPECT_EQ(w->value.ToUint64(), 1u);
  auto* bus = f.ctx.FindVariable("bus");
  ASSERT_NE(bus, nullptr);
  EXPECT_EQ(bus->value.ToUint64(), 0x55u);
}

// §10.6.1: "Releasing a variable that ... currently has an active assign
// procedural continuous assignment shall reestablish that assignment", and the
// assignment being reestablished is `assign {a, b} = 16'h1234`. What that
// assignment gives `a` is §11.4.12's packed vector of bits' high half, 8'h12,
// however the release that reestablishes it is written.
//
// This release names `a` where the assign named the concatenation, and that is
// the whole of the case: the variable recorded the right-hand expression and
// not the window it was installed with, so the release recomputed a window from
// its own target -- the whole of `a`, which takes the whole of the value -- and
// reestablished all sixteen bits of 16'h1234 on the eight-bit `a`. The sibling
// case above releases the same concatenation the assign named, where the
// recomputed window happens to match and nothing separates the two.
//
// `a` reading 16'h1234 is that whole value and `a` reading 8'h34 would be it
// truncated into eight bits, so the assertion tells the slice from both wrong
// answers; `b` is asserted with it because the release named neither `b` nor
// anything of it.
TEST(ForceReleaseSim, ReleaseOfOneElementReestablishesThatElementsSlice) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hA1;\n"
      "    b = 8'hB2;\n"
      "    assign {a, b} = 16'h1234;\n"
      "    force a = 8'h55;\n"
      "    release a;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0x12u);
  EXPECT_EQ(b->value.ToUint64(), 0x34u);
}

// §10.6.1 has the reestablished assignment go on being an assignment: it
// "shall reestablish that assignment and schedule a reevaluation", so a later
// change of the right-hand side reaches the released element again, through the
// same window. Each element carries its own, and releasing one says nothing
// about the other -- `b` was never named by the force or the release and its
// half of the assign stands untouched throughout.
//
// The source is a variable rather than a literal for exactly that: with a
// constant right-hand side the reestablishment is a single write and nothing
// after it can tell a window that was recorded from one that was recomputed.
// After src becomes 16'hABCD the two elements must read 8'hAB and 8'hCD; a
// reestablishment through the whole value leaves `a` holding all sixteen bits.
TEST(ForceReleaseSim, ReleaseOfOneElementLeavesTheOtherElementsAssignIntact) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [15:0] src;\n"
      "  initial begin\n"
      "    src = 16'h1234;\n"
      "    assign {a, b} = src;\n"
      "    force a = 8'h55;\n"
      "    release a;\n"
      "    src = 16'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0xABu);
  EXPECT_EQ(b->value.ToUint64(), 0xCDu);
}

}  // namespace
