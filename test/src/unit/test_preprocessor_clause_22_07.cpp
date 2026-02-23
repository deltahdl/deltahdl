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

static std::string PreprocessWithPP(const std::string &src, PreprocFixture &f,
                                    Preprocessor &pp) {
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
// Helper: preprocess source and return timescale state.
struct PreprocResult31402 {
  SourceManager mgr;
  TimeScale timescale;
  TimeUnit global_precision;
  bool has_timescale;
  bool has_errors;
};

static PreprocResult31402 Preprocess(const std::string &src) {
  PreprocResult31402 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  preproc.Preprocess(fid);
  result.timescale = preproc.CurrentTimescale();
  result.global_precision = preproc.GlobalPrecision();
  result.has_timescale = preproc.HasTimescale();
  result.has_errors = diag.HasErrors();
  return result;
}

// Helper: parse source and return the compilation unit.
struct ParseResult31402 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult31402 Parse(const std::string &src) {
  ParseResult31402 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM §3.14.2 — Specifying time units and precision
// =============================================================================
// 24. Way 1: `timescale compiler directive specifies both time unit and
TEST(ParserClause03, Cl3_14_2_TimescaleDirectiveSetsUnitAndPrecision) {
  auto r = Preprocess("`timescale 1ns / 1ps\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r.timescale.magnitude, 1);
  EXPECT_EQ(r.timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(r.timescale.prec_magnitude, 1);
}

// 27. `timescale handles all six time units from Table 3-1.
TEST(ParserClause03, Cl3_14_2_TimescaleAllSixUnits) {
  auto r_s = Preprocess("`timescale 1s / 1s\n");
  EXPECT_EQ(r_s.timescale.unit, TimeUnit::kS);
  auto r_ms = Preprocess("`timescale 1ms / 1ms\n");
  EXPECT_EQ(r_ms.timescale.unit, TimeUnit::kMs);
  auto r_us = Preprocess("`timescale 1us / 1us\n");
  EXPECT_EQ(r_us.timescale.unit, TimeUnit::kUs);
  auto r_ns = Preprocess("`timescale 1ns / 1ns\n");
  EXPECT_EQ(r_ns.timescale.unit, TimeUnit::kNs);
  auto r_ps = Preprocess("`timescale 1ps / 1ps\n");
  EXPECT_EQ(r_ps.timescale.unit, TimeUnit::kPs);
  auto r_fs = Preprocess("`timescale 1fs / 1fs\n");
  EXPECT_EQ(r_fs.timescale.unit, TimeUnit::kFs);
}

