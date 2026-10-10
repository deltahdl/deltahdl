#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_preprocessor.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_reported_error.h"
#include "parser/time_resolve.h"
#include "preprocessor/preprocessor.h"

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

// §3.14.3: the global precision is the finest precision written anywhere in
// the design, and a `resetall (§22.3) returns only the directive state for the
// text after it; the `timescale read before it is still part of the design.
TEST(Preprocessor, GlobalPrecisionKeptAcrossResetall) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`timescale 1ns / 1ps\n"
      "module a; endmodule\n"
      "`resetall\n",
      f, pp);
  EXPECT_FALSE(pp.HasTimescale());
  EXPECT_TRUE(pp.HasGlobalPrecision());
  EXPECT_EQ(pp.GlobalPrecision(), TimeUnit::kPs);
}

TEST(Preprocessor, CoarserTimescaleAfterResetallKeepsFinerPrecision) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`timescale 1ns / 1ps\n"
      "`resetall\n"
      "`timescale 1us / 1ns\n",
      f, pp);
  EXPECT_TRUE(pp.HasTimescale());
  EXPECT_TRUE(pp.HasGlobalPrecision());
  EXPECT_EQ(pp.GlobalPrecision(), TimeUnit::kPs);
}

TEST(Preprocessor, NoTimescaleGivesNoGlobalPrecision) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`resetall\nmodule a; endmodule\n", f, pp);
  EXPECT_FALSE(pp.HasGlobalPrecision());
}

TEST(DesignBuildingBlockParsing, TimescaleBeforeResetallSetsGlobalPrecision) {
  auto r = ParseTimescale31402(
      "`timescale 1ns / 1ps\n"
      "module a; endmodule\n"
      "`resetall\n"
      "module top;\n"
      "  timeunit 1ns; timeprecision 1ns;\n"
      "  a u();\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);

  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

TEST(Preprocessor, DelayToTicks_Basic) {
  TimeScale ts;
  ts.unit = TimeUnit::kNs;
  ts.magnitude = 1;

  EXPECT_EQ(DelayToTicks(10, ts, TimeUnit::kPs), 10000);
}

TEST(Preprocessor, Timescale_StepRejectedAsUnit) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1step / 1ns\n", f, pp);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "step cannot be used to set or modify the time unit or precision", 1,
      "3.14.3"));
}

TEST(Preprocessor, Timescale_StepRejectedAsPrecision) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns / 1step\n", f, pp);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "step cannot be used to set or modify the time unit or precision", 1,
      "3.14.3"));
}

}  // namespace
