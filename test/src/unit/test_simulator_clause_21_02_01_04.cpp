#include <gtest/gtest.h>

#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Builds a NetStrength from the drive-0 and drive-1 strength ranges so a test
// can describe exactly the strength state §21.2.1.4 renders.
NetStrength MakeNS(Strength s0_hi, Strength s0_lo, Strength s1_hi,
                   Strength s1_lo) {
  NetStrength ns;
  ns.s0_hi = s0_hi;
  ns.s0_lo = s0_lo;
  ns.s1_hi = s1_hi;
  ns.s1_lo = s1_lo;
  return ns;
}

// Runs a single-module source through elaboration and simulation while
// capturing stdout, so a %v rendering produced by $display can be inspected.
std::string CaptureDisplayOutput(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// §21.2.1.4: the strength of a scalar net is reported in a three-character
// format. Each of the renderings below is exactly three characters wide --
// two strength characters followed by one logic-value character.
TEST(StrengthFormat, RenderingIsAlwaysThreeCharacters) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kStrong, Strength::kStrong))
                .size(),
            3u);
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kPull, Strength::kMedium,
                                  Strength::kHighz, Strength::kHighz))
                .size(),
            3u);
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kHighz, Strength::kHighz))
                .size(),
            3u);
}

// Table 21-5: a strong drive of a logic 1 renders with the St mnemonic and the
// 1 logic-value character.
TEST(StrengthFormat, StrongDriveOneIsSt1) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kStrong, Strength::kStrong)),
            "St1");
}

// Table 21-5: a pull drive of a logic 0 renders as Pu0.
TEST(StrengthFormat, PullDriveZeroIsPu0) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kPull, Strength::kPull,
                                  Strength::kHighz, Strength::kHighz)),
            "Pu0");
}

// §21.2.1.4: the high-impedance strength cannot carry a known logic value; the
// only logic value allowed at this level is Z, so a fully undriven net renders
// as HiZ.
TEST(StrengthFormat, UndrivenNetIsHiZ) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kHighz, Strength::kHighz)),
            "HiZ");
}

// Table 21-5: a 0-valued charge stored on a medium capacitor renders as Me0.
TEST(StrengthFormat, MediumCapacitorZeroIsMe0) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kMedium, Strength::kMedium,
                                  Strength::kHighz, Strength::kHighz)),
            "Me0");
}

// §21.2.1.4 / Table 21-5: an unknown value whose 0 and 1 components sit at one
// common strength level uses that level's mnemonic, here strong -> StX.
TEST(StrengthFormat, StrongUnknownSameLevelIsStX) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kStrong, Strength::kStrong,
                                  Strength::kStrong, Strength::kStrong)),
            "StX");
}

// §21.2.1.4 / Table 21-5: a value that is ambiguously a pull-driven 1 or high
// impedance is the H logic value, and L/H always use a mnemonic -> PuH.
TEST(StrengthFormat, PullOneOrHighZIsPuH) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kPull, Strength::kHighz)),
            "PuH");
}

// §21.2.1.4 / Table 21-5: an unknown value whose 0 and 1 components are at
// different strength levels prints the two levels as decimal digits in 0-then-1
// order, followed by X -- a strong (6) 0 and a pull (5) 1 give 65X.
TEST(StrengthFormat, UnknownDifferentLevelsIs65X) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kStrong, Strength::kStrong,
                                  Strength::kPull, Strength::kPull)),
            "65X");
}

// §21.2.1.4: for an unknown value at differing levels the two digits are the
// 0-side level then the 1-side level, in that order -- not sorted by magnitude.
// Here the 0 side is the weaker pull (5) and the 1 side the stronger strong
// (6), so the rendering must read 56X; a magnitude-sorted implementation would
// wrongly emit 65X. This complements the descending 65X case to pin the order.
TEST(StrengthFormat, UnknownDifferentLevelsKeepsZeroThenOneOrder) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kPull, Strength::kPull,
                                  Strength::kStrong, Strength::kStrong)),
            "56X");
}

// §21.2.1.4 / Table 21-5: a logic 0 driven across a range of strengths prints
// the maximum then minimum level as decimal digits -- pull (5) down to medium
// (2) gives 520.
TEST(StrengthFormat, ZeroAcrossRangeIs520) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kPull, Strength::kMedium,
                                  Strength::kHighz, Strength::kHighz)),
            "520");
}

// §21.2.1.4: a logic 1 driven across a range of strengths likewise prints the
// maximum then minimum level -- strong (6) down to pull (5) gives 651.
TEST(StrengthFormat, OneAcrossRangeIsDigitsThenValue) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kStrong, Strength::kPull)),
            "651");
}

// Table 21-3: the L logic value means "logic 0 or high impedance". A 0 side
// whose strength reaches down to highz is ambiguous between driving 0 and
// floating, and L always uses a mnemonic for the strength level -> StL.
TEST(StrengthFormat, ZeroOrHighZIsMnemonicL) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kStrong, Strength::kHighz,
                                  Strength::kHighz, Strength::kHighz)),
            "StL");
}

// Table 21-4: every strength-level mnemonic is reachable. Su (supply, 7), La
// (large capacitor, 4), We (weak, 3), and Sm (small, 1) complete the set
// alongside St/Pu/Me/Hi exercised above.
TEST(StrengthFormat, AllStrengthLevelMnemonicsAreReachable) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kSupply, Strength::kSupply)),
            "Su1");
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kLarge, Strength::kLarge,
                                  Strength::kHighz, Strength::kHighz)),
            "La0");
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kWeak, Strength::kWeak)),
            "We1");
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kSmall, Strength::kSmall,
                                  Strength::kHighz, Strength::kHighz)),
            "Sm0");
}

// §21.2.1.4: for each %v in a string literal, a corresponding scalar reference
// follows in the argument list. The dispatcher must therefore consume one
// argument per %v and substitute that argument's strength rendering in order.
TEST(StrengthFormat, PercentVConsumesOneArgumentEach) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 1, 1),
                              MakeLogic4VecVal(arena, 1, 0)};
  std::vector<std::string> v_fmts{"St1", "Pu0"};
  auto out = FormatDisplay("a=%v b=%v", vals, {.v_fmts = &v_fmts});
  EXPECT_EQ(out, "a=St1 b=Pu0");
}

// Table 21-1 gives every specifier in both cases ("%v or %V"); the uppercase
// form must route to the same strength substitution as the lowercase one.
TEST(StrengthFormat, PercentVUppercaseMatchesLowercase) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 1, 0)};
  std::vector<std::string> v_fmts{"StX"};
  EXPECT_EQ(FormatDisplay("%V", vals, {.v_fmts = &v_fmts}),
            FormatDisplay("%v", vals, {.v_fmts = &v_fmts}));
}

// End-to-end: a wire driven to a known logic 1 by a continuous assignment
// resolves to a strong drive, and FormatStrength renders that resolved net
// strength as St1.
TEST(StrengthFormat, ResolvedNetStrengthRendersStrongDriveOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("w");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(FormatStrength(net->resolved_strength), "St1");
}

// End-to-end: the same net driven to a known logic 0 renders as St0.
TEST(StrengthFormat, ResolvedNetStrengthRendersStrongDriveZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("w");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(FormatStrength(net->resolved_strength), "St0");
}

// End-to-end through the display path: $display("%v", net) prints the scalar
// net's three-character strength rendering.
TEST(StrengthFormat, DisplayPercentVPrintsNetStrength) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "  initial #1 $display(\"%v\", w);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("St1"), std::string::npos);
}

// §21.2.1.4: each %v consumes exactly one argument from the list. Edge case --
// even when no strength rendering is available for that argument, the %v still
// consumes its slot, so a following specifier binds to the next argument. Here
// the %v eats the first value (5, which is therefore never printed) and the %d
// binds to the second, proving the per-%v argument advance.
TEST(StrengthFormat, PercentVConsumesItsArgumentWithoutAStrengthString) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 8, 5),
                              MakeLogic4VecVal(arena, 8, 9)};
  std::vector<std::string> v_fmts{""};
  auto out = FormatDisplay("%v=%d", vals, {.v_fmts = &v_fmts});
  // The 5 was consumed by the %v (which had no strength string), so it never
  // prints; the %d therefore binds to the second argument, 9.
  EXPECT_EQ(out.find('5'), std::string::npos);
  EXPECT_NE(out.find('9'), std::string::npos);
}

// Error/edge case: a %v with no corresponding argument supplied must neither
// crash nor leave a stray percent sign -- it simply renders nothing.
TEST(StrengthFormat, PercentVWithoutArgumentEmitsNothing) {
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%v", vals);
  EXPECT_TRUE(out.empty());
}

// End-to-end edge case: an undriven scalar net has no driver, so its resolved
// strength stays at the high-impedance level, which §21.2.1.4 reports as HiZ.
TEST(StrengthFormat, UndrivenWireDisplaysAsHiZ) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module m;\n"
      "  wire w;\n"
      "  initial #1 $display(\"%v\", w);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("HiZ"), std::string::npos);
}

// End-to-end edge case: %v targets scalar nets. An operand that names a
// variable rather than a net has no strength model, so the production lookup
// finds no net and the specifier renders nothing between the surrounding
// literal text.
TEST(StrengthFormat, NonNetOperandToPercentVRendersEmpty) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module m;\n"
      "  reg r;\n"
      "  initial begin\n"
      "    r = 1'b1;\n"
      "    $display(\"[%v]\", r);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("[]"), std::string::npos);
}

}  // namespace
