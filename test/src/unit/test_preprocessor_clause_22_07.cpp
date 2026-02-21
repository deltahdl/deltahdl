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

TEST(Preprocessor, Timescale_GlobalPrecision) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns / 1ns\n", f, pp);
  EXPECT_EQ(pp.GlobalPrecision(), TimeUnit::kNs);
  PreprocessWithPP("`timescale 1us / 1ps\n", f, pp);
  // Global precision is the finest (most negative exponent).
  EXPECT_EQ(pp.GlobalPrecision(), TimeUnit::kPs);
}

TEST(Preprocessor, Timescale_InvalidUnit) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1xx / 1ns\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DelayToTicks_Basic) {
  TimeScale ts;
  ts.unit = TimeUnit::kNs;
  ts.magnitude = 1;
  // 10 delay units at 1ns with 1ps precision = 10,000 ticks.
  EXPECT_EQ(DelayToTicks(10, ts, TimeUnit::kPs), 10000);
}

TEST(Preprocessor, DelayToTicks_Magnitude) {
  TimeScale ts;
  ts.unit = TimeUnit::kUs;
  ts.magnitude = 100;
  // 5 delay units at 100us with 1ns precision = 5 * 100 * 1000 = 500,000 ticks.
  EXPECT_EQ(DelayToTicks(5, ts, TimeUnit::kNs), 500000);
}
