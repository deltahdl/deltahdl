// §22.7: `timescale

#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct PreprocFixture {
  SourceManager mgr;
  DiagEngine diag{mgr};
};

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

namespace {

TEST(Preprocessor, Timescale_ParseBasic) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns / 1ps\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.CurrentTimescale().unit, TimeUnit::kNs);
  EXPECT_EQ(pp.CurrentTimescale().magnitude, 1);
  EXPECT_EQ(pp.CurrentTimescale().precision, TimeUnit::kPs);
  EXPECT_EQ(pp.CurrentTimescale().prec_magnitude, 1);
}

TEST(Preprocessor, Timescale_ParseMagnitude) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 100us / 10ns\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.CurrentTimescale().unit, TimeUnit::kUs);
  EXPECT_EQ(pp.CurrentTimescale().magnitude, 100);
  EXPECT_EQ(pp.CurrentTimescale().precision, TimeUnit::kNs);
  EXPECT_EQ(pp.CurrentTimescale().prec_magnitude, 10);
}

TEST(Preprocessor, Timescale_InvalidUnit) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1xx / 1ns\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DelayToTicks_Magnitude) {
  TimeScale ts;
  ts.unit = TimeUnit::kUs;
  ts.magnitude = 100;
  // 5 delay units at 100us with 1ns precision = 5 * 100 * 1000 = 500,000 ticks.
  EXPECT_EQ(DelayToTicks(5, ts, TimeUnit::kNs), 500000);
}

// 39. No `timescale: has_timescale is false; default timescale values.
TEST(ParserClause03, Cl3_14_2_1_NoTimescaleDefault) {
  auto r = Preprocess("// no directives\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.has_timescale);
  // Default TimeScale struct values (ns/ns).
  EXPECT_EQ(r.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r.timescale.precision, TimeUnit::kNs);
}

// 42. Error: invalid time unit string.
TEST(ParserClause03, Cl3_14_2_1_ErrorInvalidUnit) {
  auto r = Preprocess("`timescale 1xx / 1ps\n");
  EXPECT_TRUE(r.has_errors);
}

// 43. Delay conversion uses `timescale values.  A delay of 1 under
// `timescale 10ns/1ns converts to 10 ticks at ns global precision.
TEST(ParserClause03, Cl3_14_2_1_DelayConversionWithTimescale) {
  auto r = Preprocess("`timescale 10ns / 1ns\n");
  EXPECT_FALSE(r.has_errors);
  // A delay of 3 in this timescale = 3 * 10ns = 30ns = 30 ticks at ns.
  EXPECT_EQ(DelayToTicks(3, r.timescale, r.global_precision), 30u);
  // Real delay 1.5 = 1.5 * 10ns = 15ns, rounded to 1ns step = 15 ticks.
  EXPECT_EQ(RealDelayToTicks(1.5, r.timescale, r.global_precision), 15u);
}

}  // namespace
