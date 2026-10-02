#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

// LRM 19.5.3: automatic bins are created for an integral coverpoint only; a
// real coverpoint never receives them.
TEST(AutoBinCreation, NotAllowedForRealCoverpoint) {
  CoverPoint integral;
  CoverPoint real_cp;
  real_cp.is_real = true;
  EXPECT_TRUE(CoverageDB::AutoBinsAllowed(&integral));
  EXPECT_FALSE(CoverageDB::AutoBinsAllowed(&real_cp));
}

// LRM 19.5.3: AutoCreateBins on a real coverpoint produces no bins.
TEST(AutoBinCreation, RealCoverpointGetsNoAutoBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "r");
  cp->is_real = true;
  cp->auto_bin_count = 4;

  CoverageDB::AutoCreateBins(cp, 0, 15);
  EXPECT_TRUE(cp->bins.empty());
}

// LRM 19.5.3: for a non-enumeration integral coverpoint, N is the minimum of
// 2^M and the auto_bin_max option, M being the number of bits to represent the
// coverpoint.
TEST(AutoBinCreation, CountIsMinOfTwoPowMAndAutoBinMax) {
  // 2^8 = 256 exceeds the limit, so auto_bin_max wins.
  EXPECT_EQ(CoverageDB::AutoBinCount(8, 64), 64u);
  // 2^2 = 4 is below the limit, so the representable-value count wins.
  EXPECT_EQ(CoverageDB::AutoBinCount(2, 64), 4u);
  // Equal: either value yields the same count.
  EXPECT_EQ(CoverageDB::AutoBinCount(6, 64), 64u);
}

// LRM 19.5.3: for an enumeration coverpoint, N is the cardinality of the
// enumeration and the auto_bin_max limit does not apply.
TEST(AutoBinCreation, EnumCountIsCardinality) {
  EXPECT_EQ(CoverageDB::AutoBinCountEnum(3), 3u);
  EXPECT_EQ(CoverageDB::AutoBinCountEnum(257), 257u);
}

// LRM 19.5.3: the number of automatically created bins equals AutoBinCount, the
// same N that is the denominator of the automatic-bin coverpoint coverage of
// LRM 19.11.1 — the two subclauses share this count.
TEST(AutoBinCreation, BinCountMatchesAutoBinCount) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;  // auto_bin_max in effect

  CoverageDB::AutoCreateBins(cp, 0, 3);  // M = 2 bits, 2^M = 4 values
  EXPECT_EQ(cp->bins.size(), CoverageDB::AutoBinCount(2, 4));
}

// LRM 19.5.3: when 2^M does not divide evenly by N, the 2^M values are
// distributed across the N bins with the last bin absorbing the remaining
// items — M=3, N=3 yields [0:1], [2:3], [4:7].
TEST(AutoBinCreation, LastBinAbsorbsRemainder) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 3;

  CoverageDB::AutoCreateBins(cp, 0, 7);  // M = 3, 2^M = 8 values, N = 3

  ASSERT_EQ(cp->bins.size(), 3u);
  EXPECT_EQ(cp->bins[0].ranges, (std::vector<CoverValueRange>{{0, 1}}));
  EXPECT_EQ(cp->bins[1].ranges, (std::vector<CoverValueRange>{{2, 3}}));
  EXPECT_EQ(cp->bins[2].ranges, (std::vector<CoverValueRange>{{4, 7}}));
}

// LRM 19.5.3: each automatic bin is named "auto[value]" for a single value and
// "auto[low:high]" for a range.
TEST(AutoBinCreation, BinNamesEmbedValueOrRange) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 3;

  CoverageDB::AutoCreateBins(cp, 0, 7);

  ASSERT_EQ(cp->bins.size(), 3u);
  EXPECT_EQ(cp->bins[0].name, "auto[0:1]");
  EXPECT_EQ(cp->bins[1].name, "auto[2:3]");
  EXPECT_EQ(cp->bins[2].name, "auto[4:7]");
}

// LRM 19.5.3: a bin that holds a single coverage point value is named after
// that single value.
TEST(AutoBinCreation, SingleValueBinNamesUseTheValue) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;

  CoverageDB::AutoCreateBins(cp, 0, 3);  // 4 bins, one value each

  ASSERT_EQ(cp->bins.size(), 4u);
  EXPECT_EQ(cp->bins[0].name, "auto[0]");
  EXPECT_EQ(cp->bins[3].name, "auto[3]");
}

// LRM 19.5.3: for an enumerated type the bin name embeds the named constant
// associated with the enumerated value.
TEST(AutoBinCreation, EnumBinNameUsesNamedConstant) {
  EXPECT_EQ(CoverageDB::AutoEnumBinName("RED"), "auto[RED]");
}

// LRM 19.5.3: automatically created bins consider 2-state values only; a sample
// whose value contains x or z is excluded.
TEST(AutoBinCreation, SampleWithXZExcluded) {
  EXPECT_TRUE(CoverageDB::AutoBinSampleIncluded(/*sample_has_xz=*/false));
  EXPECT_FALSE(CoverageDB::AutoBinSampleIncluded(/*sample_has_xz=*/true));
}

// LRM 19.5.3 (edge): when 2^M divides evenly by N, every bin holds the same
// number of values — eight values across four bins give [0:1], [2:3], [4:5],
// [6:7] with no remainder to absorb.
TEST(AutoBinCreation, EvenDivisionDistributesValuesEqually) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;

  CoverageDB::AutoCreateBins(cp, 0, 7);  // 8 values, N = 4

  ASSERT_EQ(cp->bins.size(), 4u);
  EXPECT_EQ(cp->bins[0].ranges, (std::vector<CoverValueRange>{{0, 1}}));
  EXPECT_EQ(cp->bins[1].ranges, (std::vector<CoverValueRange>{{2, 3}}));
  EXPECT_EQ(cp->bins[2].ranges, (std::vector<CoverValueRange>{{4, 5}}));
  EXPECT_EQ(cp->bins[3].ranges, (std::vector<CoverValueRange>{{6, 7}}));
}

// LRM 19.5.3 (edge): when the auto_bin_max limit exceeds the number of
// representable values (2^M), N collapses to 2^M, yielding one bin per value.
TEST(AutoBinCreation, BinCountClampedToValueCountWhenCapExceedsRange) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 64;  // far above the 4 representable values

  CoverageDB::AutoCreateBins(cp, 0, 3);  // 2^M = 4

  ASSERT_EQ(cp->bins.size(), 4u);
  EXPECT_EQ(cp->bins[0].ranges, (std::vector<CoverValueRange>{{0, 0}}));
  EXPECT_EQ(cp->bins[3].ranges, (std::vector<CoverValueRange>{{3, 3}}));
}

// LRM 19.5.3 (edge): for a coverpoint wide enough that 2^M is astronomically
// large, the auto_bin_max limit determines N. The bit count is capped without
// overflowing the 2^M computation.
TEST(AutoBinCreation, WideCoverpointCountCappedByAutoBinMax) {
  EXPECT_EQ(CoverageDB::AutoBinCount(64, 100), 100u);
  EXPECT_EQ(CoverageDB::AutoBinCount(63, 100), 100u);
}

// LRM 19.5.3: automatic state bins are created for an integral coverpoint that
// defines no bins except ignore or illegal bins. A coverpoint carrying only
// ignore/illegal bins is still eligible, and auto bins are added alongside
// them.
TEST(AutoBinCreation, IgnoreAndIllegalBinsDoNotSuppressAutoBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;

  CoverBin ignore;
  ignore.kind = CoverBinKind::kIgnore;
  ignore.values = {7, 8};
  CoverageDB::AddBin(cp, ignore);
  CoverBin illegal;
  illegal.kind = CoverBinKind::kIllegal;
  illegal.values = {9};
  CoverageDB::AddBin(cp, illegal);

  EXPECT_TRUE(CoverageDB::ShouldAutoCreateBins(cp));
  CoverageDB::AutoCreateBins(cp, 0, 3);  // 4 representable values

  // The two subtractive bins remain and four auto bins are appended.
  int auto_bins = 0;
  for (const auto& b : cp->bins) {
    if (b.kind == CoverBinKind::kAuto) ++auto_bins;
  }
  EXPECT_EQ(auto_bins, 4);
}

// LRM 19.5.3: a coverpoint that already defines a user bin (here an explicit
// value bin) does not receive automatic bins.
TEST(AutoBinCreation, UserDefinedBinSuppressesAutoBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;

  CoverBin user;
  user.kind = CoverBinKind::kExplicit;
  user.values = {1, 2};
  CoverageDB::AddBin(cp, user);

  EXPECT_FALSE(CoverageDB::ShouldAutoCreateBins(cp));
  CoverageDB::AutoCreateBins(cp, 0, 3);

  // No auto bins were added; only the single explicit bin remains.
  ASSERT_EQ(cp->bins.size(), 1u);
  EXPECT_EQ(cp->bins[0].kind, CoverBinKind::kExplicit);
}

// LRM 19.5.3: a coverpoint with no bins at all is eligible for automatic bin
// creation.
TEST(AutoBinCreation, EmptyCoverpointIsEligible) {
  CoverPoint cp;
  EXPECT_TRUE(CoverageDB::ShouldAutoCreateBins(&cp));
}

// LRM 19.5.3: a real coverpoint is never eligible for automatic bin creation,
// regardless of its bins.
TEST(AutoBinCreation, RealCoverpointNotEligible) {
  CoverPoint cp;
  cp.is_real = true;
  EXPECT_FALSE(CoverageDB::ShouldAutoCreateBins(&cp));
}

// LRM 19.5.3: the "no bins except ignored or illegal" test admits an ignore bin
// as the sole bin — an ignore-only coverpoint still receives automatic bins.
TEST(AutoBinCreation, IgnoreOnlyBinsDoNotSuppressAutoBins) {
  CoverPoint cp;
  CoverBin ignore;
  ignore.kind = CoverBinKind::kIgnore;
  ignore.values = {5};
  cp.bins.push_back(ignore);
  EXPECT_TRUE(CoverageDB::ShouldAutoCreateBins(&cp));
}

// LRM 19.5.3: an illegal bin as the sole bin likewise leaves the coverpoint
// eligible for automatic bin creation.
TEST(AutoBinCreation, IllegalOnlyBinsDoNotSuppressAutoBins) {
  CoverPoint cp;
  CoverBin illegal;
  illegal.kind = CoverBinKind::kIllegal;
  illegal.values = {5};
  cp.bins.push_back(illegal);
  EXPECT_TRUE(CoverageDB::ShouldAutoCreateBins(&cp));
}

// LRM 19.5.3: a wildcard bin is a user-defined bin, so its presence suppresses
// automatic bin creation.
TEST(AutoBinCreation, WildcardBinSuppressesAutoBins) {
  CoverPoint cp;
  CoverBin wildcard;
  wildcard.kind = CoverBinKind::kWildcard;
  wildcard.values = {1};
  cp.bins.push_back(wildcard);
  EXPECT_FALSE(CoverageDB::ShouldAutoCreateBins(&cp));
}

// LRM 19.5.3: a transition bin is a user-defined bin and suppresses automatic
// bin creation.
TEST(AutoBinCreation, TransitionBinSuppressesAutoBins) {
  CoverPoint cp;
  CoverBin transition;
  transition.kind = CoverBinKind::kTransition;
  transition.transitions = {{1, 2}};
  cp.bins.push_back(transition);
  EXPECT_FALSE(CoverageDB::ShouldAutoCreateBins(&cp));
}

// LRM 19.5.3: a default bin is a user-defined bin and suppresses automatic bin
// creation.
TEST(AutoBinCreation, DefaultBinSuppressesAutoBins) {
  CoverPoint cp;
  CoverBin dflt;
  dflt.kind = CoverBinKind::kDefault;
  cp.bins.push_back(dflt);
  EXPECT_FALSE(CoverageDB::ShouldAutoCreateBins(&cp));
}

// §19.5.3: a coverpoint with no bins gets automatic bins, one per value of a
// two-bit expression since 4 is under auto_bin_max. Sampling 0 and 2 covers
// two of the four.
TEST(CovergroupInstanceSim, AutomaticBinsFromDeclaration) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v;\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v = 0; c.sample();\n"
                       "    v = 2; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=2 t=4\n");
}

// §19.5.3: the automatic bins of a signed coverpoint span its signed range,
// so an int coverpoint's 64 bins take -5 into one of them; an unlabelled
// coverpoint of an expression gets its automatic bins too, v ^ 3 sampling 3.
TEST(CovergroupInstanceSim, SignedAndExpressionCoverpointsAutomaticBins) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  byte i; bit [1:0] v; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint i;\n"
                       "    coverpoint v ^ 2'b11;\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    i = -5; v = 0; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=2 t=68\n");
}

// §19.5.3: the 64 automatic bins of an int coverpoint split all 2^32 of its
// values among them, so -5 falls in the 32nd, the bin ending at -1.
TEST(CovergroupInstanceSim, AutomaticBinsOfIntSpanEveryValue) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  int i; int n, t;\n"
          "  covergroup cg;\n"
          "    coverpoint i;\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin i = -5; c.sample(); void'(c.get_inst_coverage(n, "
          "t)); $display(\"n=%0d t=%0d\", n, t); end\n"
          "endmodule\n",
          f),
      "n=1 t=64\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.5.3: a coverpoint of an enumeration type gets one automatic bin for each
// named constant, auto[RED], auto[GREEN] and auto[BLUE], rather than bins over
// the 32-bit range of its base type.
TEST(CovergroupInstanceSim, EnumCoverpointGetsOneAutomaticBinPerConstant) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                       "  color_t col; int n, t;\n"
                       "  covergroup cg; coverpoint col; endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin col = GREEN; c.sample(); "
                       "void'(c.get_inst_coverage(n, t)); $display(\"n=%0d "
                       "t=%0d\", n, t); end\n"
                       "endmodule\n",
                       f),
            "n=1 t=3\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.5.3: automatically created bins consider 2-state values only, so the
// sample 2'bx0 is counted in none of the four bins of v.
TEST(CovergroupInstanceSim, SampleHoldingUnknownBitsFallsInNoAutomaticBin) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  logic [1:0] v; int n, t;\n"
          "  covergroup cg; coverpoint v; endgroup\n"
          "  cg c = new;\n"
          "  initial begin v = 2'bx0; c.sample(); void'(c.get_inst_coverage(n, "
          "t)); $display(\"n=%0d t=%0d\", n, t); end\n"
          "endmodule\n",
          f),
      "n=0 t=4\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
