#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_parser.h"
#include "fixture_preprocessor.h"
#include "fixture_preprocessor_timescale.h"

using namespace delta;

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

  EXPECT_EQ(DelayToTicks(5, ts, TimeUnit::kNs), 500000);
}

TEST(ParserClause03, Cl3_14_2_1_NoTimescaleDefault) {
  auto r = Preprocess("// no directives\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.has_timescale);

  EXPECT_EQ(r.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r.timescale.precision, TimeUnit::kNs);
}

TEST(ParserClause03, Cl3_14_2_1_ErrorInvalidUnit) {
  auto r = Preprocess("`timescale 1xx / 1ps\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserClause03, Cl3_14_2_1_DelayConversionWithTimescale) {
  auto r = Preprocess("`timescale 10ns / 1ns\n");
  EXPECT_FALSE(r.has_errors);

  EXPECT_EQ(DelayToTicks(3, r.timescale, r.global_precision), 30u);

  EXPECT_EQ(RealDelayToTicks(1.5, r.timescale, r.global_precision), 15u);
}

TEST(ParserSection22, TimescaleModuleNamePreserved) {
  auto r = ParseWithPreprocessor(
      "`timescale 1ns/1ps\n"
      "module foo;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "foo");
}

}
