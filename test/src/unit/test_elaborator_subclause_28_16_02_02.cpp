#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(ChargeDecaySpecElaboration, ThirdDelayFlowsToDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(7, 11, 13) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 13u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeDecaySpecElaboration, SingleDelayDoesNotPopulateDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #50 cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 0u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §28.16.2.2's charge decay time is a net delay value, i.e. a constant
// expression (11.2.1). A parameter used as the third delay resolves in the
// module's parameter scope and flows to decay_ticks, not just a bare literal.
TEST(ChargeDecaySpecElaboration, ParameterThirdDelayResolvesToDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter integer DECAY = 21;\n"
      "  trireg #(0, 0, DECAY) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 21u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// A localparam is likewise a valid constant form for the charge decay time.
TEST(ChargeDecaySpecElaboration, LocalparamThirdDelayResolvesToDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam integer DECAY = 34;\n"
      "  trireg #(0, 0, DECAY) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 34u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeDecaySpecElaboration, TwoDelaysDoNotPopulateDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(4, 9) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 0u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §28.16.2.2 rules that "the third delay in a trireg net declaration shall
// specify the charge decay time", and §28.16.2 admits §28.16.1's three-valued
// form into that slot: "Like all nets, the delay specification in a trireg net
// declaration can contain up to three delays." §28.16.1 in turn rules that the
// "minimum, typical, and maximum values for each delay shall be specified as
// expressions separated by colons", so `#(1, 2, 3:4:5)` writes a charge decay
// time of 3, 4 or 5.
//
// 4 is the one this asserts, because 4 is the member elaboration can reach.
// §11.11 orders the three as "minimum, typical, and maximum values -- in that
// order", and the typical member is what a design elaborates with: the delay
// mode that would name a different member is DelayMode in
// src/simulator/sim_context_types.h, which only SimContext::SetDelayMode
// writes and which nothing in production calls. #3264 covers that, and until it
// is settled a case asserting 3 or 5 has no way to ask for them.
//
// The rise and fall delays are 1 and 2 so that a decay time read off the wrong
// position of the declaration answers 1 or 2 rather than one of the members,
// and a fold that gives up on the triple answers 0 -- which
// ChargeDecaySpecElaboration.SingleDelayDoesNotPopulateDecayTicks above asserts
// of a declaration carrying no third delay at all, so the triple would state
// the opposite of what it says.
TEST(ChargeDecaySpecElaboration, ThirdDelayTripleTakesTheTypicalMember) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(1, 2, 3:4:5) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* cap = FindNet(design, "t", "cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->decay_ticks, 4u);
}

// A third delay that does not fold is warned about rather than stood down to a
// decay time of zero. Zero is the value §28.16.2 leaves a declaration writing
// no third delay with, and §28.16.2.1 arms no charge decay process at it, so
// substituting it for a fold that failed makes the declaration say the opposite
// of what it wrote.
//
// The report is a warning and not an error because A.2.2.3 writes delay3 over
// mintypmax_expression rather than constant_mintypmax_expression, so a third
// delay naming a variable is not thereby illegal -- the rise and fall delays of
// the same declaration reach the run as expressions. What the source loses is
// the charge decay time, which §28.16.2.1 needs before the drivers turn off,
// and the warning is what says so.
TEST(ChargeDecaySpecElaboration,
     ThirdDelayThatDoesNotFoldIsWarnedAboutRatherThanZeroed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] leak;\n"
      "  trireg #(1, 2, leak) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "trireg charge decay time does not fold", 3,
                              "28.16.2.2"));
}

}  // namespace
