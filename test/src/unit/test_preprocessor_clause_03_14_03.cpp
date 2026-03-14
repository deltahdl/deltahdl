#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_preprocessor.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_parser_verify.h"
#include "parser/time_resolve.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

namespace {

TEST(Preprocessor, Timescale_GlobalPrecision) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns / 1ns\n", f, pp);
  EXPECT_EQ(pp.GlobalPrecision(), TimeUnit::kNs);
  PreprocessWithPP("`timescale 1us / 1ps\n", f, pp);

  EXPECT_EQ(pp.GlobalPrecision(), TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, MultipleTimescaleDirectives) {
  auto r = ParseTimescale31402(
      "`timescale 1ns / 1ns\n"
      "module a; endmodule\n"
      "`timescale 1us / 1ps\n"
      "module b; endmodule\n");
  EXPECT_FALSE(r.has_errors);

  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

TEST(DesignBuildingBlockParsing, EarlierTimescaleFinerPrecision) {
  auto r = ParseTimescale31402(
      "`timescale 1ns / 1fs\n"
      "module a; endmodule\n"
      "`timescale 1us / 1ps\n"
      "module b; endmodule\n");
  EXPECT_FALSE(r.has_errors);

  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);
}

TEST(Preprocessor, DelayToTicks_Basic) {
  TimeScale ts;
  ts.unit = TimeUnit::kNs;
  ts.magnitude = 1;

  EXPECT_EQ(DelayToTicks(10, ts, TimeUnit::kPs), 10000);
}

}  // namespace
