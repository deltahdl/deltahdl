#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
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

}  // namespace
