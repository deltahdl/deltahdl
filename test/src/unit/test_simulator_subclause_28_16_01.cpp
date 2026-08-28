#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §28.16.1 "min:typ:max delays". The syntax for delays on gate primitives, on
// nets and on continuous assignments allows three values for each of the
// rising, falling and turn-off delays, written as expressions separated by
// colons, and the syntax for a procedural delay control allows the same. There
// shall be no required relationship between the three: they can be any three
// expressions.
//
// The parser file beside this one covers what the form parses into. What is
// left to the simulator is which of the three a run uses, and that is the only
// place the last rule can be observed at all: a triple whose members are out of
// order parses whatever an implementation later does with it, and only a run
// shows whether the member written as the minimum is the one a minimum-delay
// run waited out.

// Elaborates and runs `src` under `mode` and returns the time the run settled
// at, which is when the last delayed transition was processed.
uint64_t SettleTicksUnderMode(const std::string& src, DelayMode mode) {
  SimFixture f;
  f.ctx.SetDelayMode(mode);
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return 0;
  LowerAndRun(design, f);
  return f.scheduler.CurrentTime().ticks;
}

// §28.16.1: a gate primitive's rising delay may be given as three values, and
// the run uses the one its delay mode names. The three differ, so each mode
// settles at its own time; a run using one member for every mode reports the
// same time three times.
TEST(MinTypMaxDelaySim, GateRiseDelayTripleSelectsTheMemberForTheMode) {
  const std::string kSrc =
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  and #(7:11:15) g(y, a, b);\n"
      "  initial begin a = 1'b0; b = 1'b1; #100 a = 1'b1; end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 107u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kTyp), 111u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 115u);
}

// §28.16.1: the three values are allowed for each of the rising, falling and
// turn-off delays, so a gate carrying a triple in every slot takes its turn-off
// time from the third slot's triple. The clause's own example supplies the
// values. A run reading the mode's member out of the first slot settles at 105
// or 109 instead.
TEST(MinTypMaxDelaySim, TurnOffSlotCarriesItsOwnTriple) {
  const std::string kSrc =
      "module m;\n"
      "  reg d, en;\n"
      "  wire y;\n"
      "  bufif1 #(5:7:9, 8:10:12, 15:18:21) g(y, d, en);\n"
      "  initial begin d = 1'b1; en = 1'b1; #100 en = 1'b0; end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 115u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 121u);
}

// §28.16.1 names net declarations among the positions that take three values,
// and a net's delay reaches the run by a different route from a gate's.
TEST(MinTypMaxDelaySim, NetDeclarationDelayTripleSelectsByMode) {
  const std::string kSrc =
      "module m;\n"
      "  reg a;\n"
      "  wire #(3:5:7) y = a;\n"
      "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 103u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 107u);
}

// §28.16.1 names continuous assignments too, which carry their delay on the
// assignment rather than on the net being assigned.
TEST(MinTypMaxDelaySim, ContinuousAssignmentDelayTripleSelectsByMode) {
  const std::string kSrc =
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  assign #(3:5:7) y = a;\n"
      "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 103u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 107u);
}

// §28.16.1: there shall be no required relationship between the three
// expressions. Written largest first, the minimum-delay run waits out 15 and
// the maximum-delay run waits out 7, because each mode takes the member at its
// own position and not the smallest or largest of the three. An implementation
// sorting or clamping the triple cannot report a minimum run settling later
// than a maximum one.
TEST(MinTypMaxDelaySim, UnorderedTripleIsUsedAsWritten) {
  const std::string kSrc =
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  and #(15:11:7) g(y, a, b);\n"
      "  initial begin a = 1'b0; b = 1'b1; #100 a = 1'b1; end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 115u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 107u);
}

// §28.16.1: the members are expressions, so a parameter may stand where a
// literal may. The clause's own procedural example is written that way, and a
// procedural delay control is the fourth position the subclause names.
TEST(MinTypMaxDelaySim, ProceduralDelayTripleTakesParameterMembers) {
  const std::string kSrc =
      "module m;\n"
      "  parameter min_hi = 97, typ_hi = 100, max_hi = 107;\n"
      "  reg clk;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    #(min_hi:typ_hi:max_hi) clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMin), 97u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kTyp), 100u);
  EXPECT_EQ(SettleTicksUnderMode(kSrc, DelayMode::kMax), 107u);
}

// §28.16.1's list reaches one more delay position through §28.16.2, which rules
// that "like all nets, the delay specification in a trireg net declaration can
// contain up to three delays" and that "the third delay shall specify the
// charge decay time". So the charge decay time may be written as three
// expressions separated by colons, and which of the three the run waits out is
// what the two runs below read back. The cases above vary the mode; this one
// cannot, because the charge decay time is settled at elaboration and nothing
// in production writes a delay mode an elaboration reads (#3264).
//
// Being settled at elaboration, the charge decay time is also not a settle time
// the run can report the way the cases above do. §28.16.2.1 supplies the
// observation instead: the charge decay process "shall begin when the drivers
// of the trireg net turn off", and it ends when "the delay specified by charge
// decay time elapses, and the trireg net makes a transition from 1 or 0 to x".
// A stored 1 that has become x is therefore a decay time that has elapsed.

// Whether bit 0 of `v` reads x, which is (aval=1, bval=1). A stored 1 reads
// (aval=1, bval=0), so this is what tells a decayed trireg from an intact one.
bool Bit0IsX(const Logic4Vec& v) {
  return (v.words[0].aval & 1u) == 1u && (v.words[0].bval & 1u) == 1u;
}

// Charges a trireg to 1, releases it at t=1 so §28.16.2.1's charge decay
// process begins, stops the run with `finish_stmt`, and answers whether the
// stored bit had decayed by then. The trireg is 64 bits wide so that the
// released driver is a full machine word of high impedance, which is the
// charge-storage condition §28.15.2 asks for; a narrower z driver is not read
// as fully floating.
bool TriregDecayedBy(const char* finish_stmt) {
  SimFixture f;
  std::string src =
      "module m;\n"
      "  logic en;\n"
      "  trireg [63:0] #(0, 0, 20:40:60) cap;\n"
      "  assign cap = en ? 64'd1 : 64'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n";
  src += finish_stmt;
  src +=
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  if (design == nullptr) return false;
  LowerAndRun(design, f);
  auto* cap = f.ctx.FindNet("cap");
  EXPECT_NE(cap, nullptr);
  if (cap == nullptr) return false;
  return Bit0IsX(cap->resolved->value);
}

// The charge decay time written as 20:40:60 is 40, the typical member -- the
// one elaboration can reach, since nothing in production writes the DelayMode
// that would name another (#3264). The trireg is released at t=1, so the decay
// fires at t=41: at t=31 the stored 1 is intact and at t=51 it has become x.
//
// Reading the field the elaborator wrote cannot make this claim, because a
// charge decay time of zero and a large one are the same field value away from
// each other and §28.16.2.1 arms no decay process at zero. The run separates
// them: an intact value at t=31 rules out the minimum member, whose decay would
// have fired at t=21, and a decayed value at t=51 rules out both zero, which
// never decays, and the maximum member, whose decay fires at t=61.
TEST(MinTypMaxDelaySim, TriregChargeDecayTimeTripleDecaysAtTheTypicalMember) {
  EXPECT_FALSE(TriregDecayedBy("    #30 $finish;\n"));
  EXPECT_TRUE(TriregDecayedBy("    #50 $finish;\n"));
}

}  // namespace
