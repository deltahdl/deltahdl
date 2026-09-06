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

// §28.16.2.1 makes the charge decay a process that ends when "the delay
// specified by charge decay time elapses, and the trireg net makes a transition
// from 1 or 0 to x", so a decay time of zero is that transition happening at
// once. §28.16.2.2 gives the *absence* of a third delay the meaning of never
// decaying. The two states shared one representation -- a decay_ticks of zero
// -- so a declaration writing zero got the opposite of what it asked for.
//
// The elaborated nets are asserted to differ in the field that now tells them
// apart, which is where the distinction is made; the two run-time cases are in
// test/src/unit/test_simulator_subclause_28_16_02.cpp.
TEST(ChargeDecaySpecElaboration, ZeroDecayTimeIsRecordedAsDecaying) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(0, 0, 0) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 0u);
      EXPECT_TRUE(net.decays);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// The other half of the same distinction, which the case above cannot state on
// its own: a declaration with no third delay records the same zero count and
// does not decay. SingleDelayDoesNotPopulateDecayTicks asserts the count and is
// what let the two states share a representation.
TEST(ChargeDecaySpecElaboration, AbsentThirdDelayIsRecordedAsNotDecaying) {
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
      EXPECT_FALSE(net.decays);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
