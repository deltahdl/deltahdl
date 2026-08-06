#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §28.16.2.1 states a runtime rule: charge decay is the cause of a 1 or 0
// stored in a trireg net transitioning to the unknown value x after a specified
// delay. The charge decay process begins when the drivers of the trireg turn
// off and the net starts to hold charge; it ends either (a) when the charge
// decay time elapses, at which point the stored 1 or 0 makes a transition to x,
// or (b) when the drivers turn on again and propagate a 1, 0, or x into the
// net.
//
// The delay that arms this process is the charge decay time -- the third net
// delay of the (rise, fall, charge_decay_time) form defined in §28.16.2.2. So
// every test here builds the trireg from that real declaration syntax and
// drives it through parse -> elaborate -> lower -> run, observing the decay (or
// its absence) performed by production (net.cpp ResolveTriregCharge /
// ScheduleDecay). A wide vector is used so the released driver is a full
// machine word of high impedance -- exactly the charge-storage condition the
// rule speaks of (a narrow z driver is not seen as fully floating; see
// §28.15.2).

bool AllBitsX(const Logic4Vec& v) {
  for (uint32_t w = 0; w < v.nwords; ++w) {
    if (v.words[w].aval != ~uint64_t{0}) return false;  // x = (aval=1, bval=1)
    if (v.words[w].bval != ~uint64_t{0}) return false;
  }
  return true;
}

// Claim 1 / end-condition (a): a 1 stored in a trireg decays to x once the
// charge decay time elapses. The driver charges the net to 1, then releases to
// z; running to completion fires the scheduled decay and every stored 1 becomes
// x.
TEST(ChargeDecayProcess, StoredOneDecaysToXAfterDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg [63:0] #(0, 0, 50) cap;\n"
      "  assign cap = en ? 64'd1 : 64'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"  // charge cap to 1
      "    #1;\n"
      "    en = 1'b0;\n"  // release: drivers off -> charge decay process begins
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(AllBitsX(cap->resolved->value));
}

// Claim 1 / end-condition (a): a 0 stored in a trireg decays to x the same way.
TEST(ChargeDecayProcess, StoredZeroDecaysToXAfterDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg [63:0] #(0, 0, 25) cap;\n"
      "  assign cap = en ? 64'd0 : 64'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"  // charge cap to 0
      "    #1;\n"
      "    en = 1'b0;\n"  // release -> charge decay process begins
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(AllBitsX(cap->resolved->value));
}

// Charge decay applies across the whole stored value: every stored bit of a
// multi-word vector transitions to x when the decay time elapses.
TEST(ChargeDecayProcess, WideVectorDecaysEveryBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg [127:0] #(0, 0, 45) cap;\n"
      "  assign cap = en ? 128'd1 : 128'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(AllBitsX(cap->resolved->value));
}

// Claim 2: the charge decay process begins only when the drivers turn off. A
// trireg that is continuously driven never starts to hold charge, so even with
// a charge decay time specified it never transitions to x -- time passing does
// not arm the process while a driver is on.
TEST(ChargeDecayProcess, ContinuouslyDrivenTriregNeverDecays) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  trireg [63:0] #(0, 0, 5) cap;\n"
      "  assign cap = 64'd1;\n"  // always driven: never enters charge storage
      "  initial #40;\n"         // let time pass well past the decay time
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_FALSE(cap->InCapacitiveState());
  EXPECT_FALSE(AllBitsX(cap->resolved->value));
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);  // still driven 1
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
}

// End-condition (b): if the drivers turn on again before the charge decay time
// elapses, the process ends and the driven value propagates into the trireg --
// no transition to x occurs. The rule admits three driven values (1, 0, or x);
// the three tests below exercise each. Here the net is charged to 1, released,
// then a driver re-asserts 0 while the decay is still pending, so the final
// value is the driven 0, not x.
TEST(ChargeDecayProcess, DriverTurningOnPropagatingZeroEndsProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  logic [63:0] val;\n"
      "  trireg [63:0] #(0, 0, 50) cap;\n"
      "  assign cap = en ? val : 64'bz;\n"
      "  initial begin\n"
      "    val = 64'd1; en = 1'b1;\n"  // charge to 1
      "    #1;\n"
      "    en = 1'b0;\n"  // release at t=1, decay armed at t=51
      "    #5;\n"
      "    val = 64'd0; en = 1'b1;\n"  // t=6 (<51): re-drive 0 -> ends via (b)
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_FALSE(AllBitsX(cap->resolved->value));
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 0u);  // driven 0, not x
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
}

// End-condition (b) with a driven 1: the net is charged to 0, released, then a
// driver re-asserts 1 while the decay is still pending. The final value is the
// driven 1 -- the process ended via (b), and the pending decay (which would
// have produced x) never fires.
TEST(ChargeDecayProcess, DriverTurningOnPropagatingOneEndsProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  logic [63:0] val;\n"
      "  trireg [63:0] #(0, 0, 50) cap;\n"
      "  assign cap = en ? val : 64'bz;\n"
      "  initial begin\n"
      "    val = 64'd0; en = 1'b1;\n"  // charge to 0
      "    #1;\n"
      "    en = 1'b0;\n"  // release at t=1, decay armed at t=51
      "    #5;\n"
      "    val = 64'd1; en = 1'b1;\n"  // t=6 (<51): re-drive 1 -> ends via (b)
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_FALSE(AllBitsX(cap->resolved->value));
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);  // driven 1, not x
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
}

// End-condition (b) with a driven x: the net is charged to 0, released, then a
// driver re-asserts x while the decay is still pending, and the run stops
// before the decay time elapses. The trireg reads x -- but that x comes from
// the driver turning on (condition b), not from charge decay (condition a),
// because the simulation is halted at t=11, well before the decay time of 50
// would fire at t=51. This distinguishes the driver-propagated x from a
// decay-produced x.
TEST(ChargeDecayProcess, DriverTurningOnPropagatingXEndsProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  logic [63:0] val;\n"
      "  trireg [63:0] #(0, 0, 50) cap;\n"
      "  assign cap = en ? val : 64'bz;\n"
      "  initial begin\n"
      "    val = 64'd0; en = 1'b1;\n"  // charge to 0
      "    #1;\n"
      "    en = 1'b0;\n"  // release at t=1, decay armed at t=51
      "    #5;\n"
      "    val = 64'bx; en = 1'b1;\n"  // t=6 (<51): re-drive x -> ends via (b)
      "    #5 $finish;\n"              // stop at t=11, before decay would fire
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_FALSE(
      cap->InCapacitiveState());  // actively driven, not storing charge
  EXPECT_TRUE(AllBitsX(cap->resolved->value));  // driver-propagated x
}

// Timing of the process: the stored value transitions to x when the charge
// decay time elapses, not at the moment the drivers turn off. The trireg is
// declared with a decay time of 50; the same source is run twice, stopping at a
// time before the decay time elapses and again at a time after it. Before the
// decay time the stored 1 is intact; after it, the stored value has become x.
static Net* RunTriregDecayUntil(const char* finish_stmt, SimFixture& f) {
  std::string src =
      "module m;\n"
      "  logic en;\n"
      "  trireg [63:0] #(0, 0, 50) cap;\n"
      "  assign cap = en ? 64'd1 : 64'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"  // charge cap to 1
      "    #1;\n"
      "    en = 1'b0;\n";  // release at t=1: decay armed to fire at t=51
  src += finish_stmt;
  src +=
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  return f.ctx.FindNet("cap");
}

TEST(ChargeDecayProcess, StoredValueIntactBeforeDelayElapses) {
  SimFixture f;
  auto* cap =
      RunTriregDecayUntil("    #10 $finish;\n", f);  // stop at t=11 < 51
  ASSERT_NE(cap, nullptr);
  EXPECT_FALSE(AllBitsX(cap->resolved->value));
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);  // still held 1
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
}

TEST(ChargeDecayProcess, StoredValueHasDecayedAfterDelayElapses) {
  SimFixture f;
  auto* cap =
      RunTriregDecayUntil("    #100 $finish;\n", f);  // stop at t=101 > 51
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(AllBitsX(cap->resolved->value));
}

// Negative form / boundary against §28.16.2.2: with no charge decay time in the
// declaration the charge decay process is never armed, so a released trireg
// holds its stored value indefinitely and never transitions to x. This is the
// weaving boundary -- the third-delay charge decay time of §28.16.2.2 is what
// enables the process this subclause describes.
TEST(ChargeDecayProcess, NoChargeDecayTimeMeansStoredValueNeverDecays) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg [63:0] cap;\n"  // no delay -> no charge decay time
      "  assign cap = en ? 64'd1 : 64'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"  // release -> charge storage, but no decay armed
      "    #100;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(cap->InCapacitiveState());
  EXPECT_FALSE(AllBitsX(cap->resolved->value));
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);  // still held 1
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
}

}  // namespace
