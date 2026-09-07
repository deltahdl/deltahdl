#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(GateDelayElaboration, NoDelayLeavesAllSlotsNull) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay, nullptr);
}

TEST(GateDelayElaboration, SingleDelayPopulatesRiseOnly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and #5 g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 5u);
  EXPECT_EQ(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay, nullptr);
}

TEST(GateDelayElaboration, TwoDelayPopulatesRiseAndFall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, a, b;\n"
      "  or #(3, 7) g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 3u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 7u);
  EXPECT_EQ(mod->assigns[0].delay_decay, nullptr);
}

TEST(GateDelayElaboration, ThreeDelayPopulatesAllSlots) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  bufif0 #(4, 6, 9) g(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 4u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 6u);
  ASSERT_NE(mod->assigns[0].delay_decay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay->int_val, 9u);
}

TEST(GateDelayElaboration, MultiOutputGateDelayAppliesToEveryOutput) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire o1, o2, in;\n"
      "  buf #(2, 4) g(o1, o2, in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->assigns.size(), 2u);
  for (size_t i = 0; i < 2; ++i) {
    ASSERT_NE(mod->assigns[i].delay, nullptr);
    EXPECT_EQ(mod->assigns[i].delay->int_val, 2u);
    ASSERT_NE(mod->assigns[i].delay_fall, nullptr);
    EXPECT_EQ(mod->assigns[i].delay_fall->int_val, 4u);
  }
}

TEST(GateDelayElaboration, MosSwitchDelayForwardsToContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire o, d, c;\n"
      "  nmos #(1, 2, 3) n1(o, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 1u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 2u);
  ASSERT_NE(mod->assigns[0].delay_decay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay->int_val, 3u);
}

TEST(GateDelayElaboration, CmosSwitchDelayForwardsToContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire o, d, nc, pc;\n"
      "  cmos #(7, 8, 9) c1(o, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 7u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 8u);
  ASSERT_NE(mod->assigns[0].delay_decay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay->int_val, 9u);
}

// §28.16 gives a delay a direction as well as a size: a net delay is "the time
// it takes from any driver on the net changing value to the time when the net
// value is updated and propagated further", and §28.16.2 gives a trireg's third
// delay as "the delay between when the drivers of a trireg net turn off and
// when its stored charge can no longer be determined". Neither runs backwards.
// The clause names no negative form, so a source that writes one is reported
// rather than reinterpreted: cast into the unsigned tick counts the model runs
// on, -5 became 18446744073709551611 and the charge decayed after six hundred
// billion years.
//
// Runs `decl` as the whole body of a module and asserts the report stands at
// the declaration's own line, so the cases differ only in the delay they write.
void ExpectDelayReported(const std::string& decl, const std::string& value) {
  ElabFixture f;
  const std::string kSrc = "module m;\n  " + decl + "\nendmodule\n";
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "delay is " + value + "; a delay is the time between two events",
      LineHolding(kSrc, decl), "28.16"));
}

// The charge decay slot, which is where the wrap was visible: it is the one
// delay the elaborator folds and stores rather than leaving as an expression.
TEST(DelaySignElaboration, NegativeTriregDecayTimeIsReported) {
  ExpectDelayReported("trireg #(0, 0, -5) c;", "-5");
}

// A transition slot of an ordinary net, which reaches the check by a different
// route: §28.16.2.2's decay time is folded at elaboration while a rise delay is
// left an expression for the run to evaluate, so a check on the folded value
// alone would pass this.
TEST(DelaySignElaboration, NegativeNetRiseDelayIsReported) {
  ExpectDelayReported("wire #(-1) w;", "-1");
}

// A gate instance's delay, so the rule reads as one rule over §28.16's delays
// rather than as a property of net declarations.
TEST(DelaySignElaboration, NegativeGateDelayIsReported) {
  ExpectDelayReported("and #(-2) g(y, a, b);", "-2");
}

// §28.16.1: "The minimum, typical, and maximum values for each delay shall be
// specified as expressions separated by colons ... These can be any three
// expressions." Which of the three is the delay is settled per run, so each is
// a delay in some run and each is checked. Reading the folded scalar instead
// would see whichever member the active mode selects -- the typical one by
// default -- and pass the negative written beside it.
TEST(DelaySignElaboration, NegativeMinimumOfAMinTypMaxDelayIsReported) {
  ExpectDelayReported("wire #(-1:2:3) w;", "-1");
}

// Zero is a delay, and §28.16.2.1 gives a decay time of zero the transition to
// x happening at once, so the check is on the sign and not on the value being
// positive. A rule written as "greater than zero" would reject this.
TEST(DelaySignElaboration, ZeroDelayIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  trireg #(0, 0, 0) c;\n"
      "  wire #(0) w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A real delay in a transition slot, which reaches the sign check by a
// different route from the decay time: §28.16.2.2's third delay is folded and
// stored at elaboration, while a rise delay is carried to the run as an
// expression, so a check that read only what was folded would pass this.
// A.2.2.3 admits the real_number and §3.14.1 rounds it, which leaves its sign
// what the source wrote.
TEST(DelaySignElaboration, NegativeRealNetDelayIsReported) {
  ExpectDelayReported("wire #(-1.5) w;", "-2");
}

// The rounding is §3.14.1's and not a truncation, which is what separates -2
// from the -1 truncating toward zero would give. Stated on a slot whose value
// no elaborated field carries, so the claim is about the fold rather than about
// what is stored.
TEST(DelaySignElaboration, RealNetDelayRoundsRatherThanTruncates) {
  ExpectDelayReported("wire #(-2.5) w;", "-3");
}

}  // namespace
