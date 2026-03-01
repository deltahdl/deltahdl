// §3.14.3: Simulation time unit

#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_preprocessor.h"

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
  // Global precision is the finest (most negative exponent).
  EXPECT_EQ(pp.GlobalPrecision(), TimeUnit::kPs);
}

struct ParseResult4c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4c Parse(const std::string& src) {
  ParseResult4c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// 29. Multiple `timescale — preprocessor tracks min; function uses it.
TEST(ParserClause03, Cl3_14_3_MultipleTimescaleDirectives) {
  auto r = Parse(
      "`timescale 1ns / 1ns\n"
      "module a; endmodule\n"
      "`timescale 1us / 1ps\n"
      "module b; endmodule\n");
  EXPECT_FALSE(r.has_errors);
  // Preprocessor global precision = min(1ns, 1ps) = 1ps.
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

// 30. Earlier `timescale with finer precision than later — global min is used.
TEST(ParserClause03, Cl3_14_3_EarlierTimescaleFinerPrecision) {
  auto r = Parse(
      "`timescale 1ns / 1fs\n"
      "module a; endmodule\n"
      "`timescale 1us / 1ps\n"
      "module b; endmodule\n");
  EXPECT_FALSE(r.has_errors);
  // Preprocessor global precision = min(1fs, 1ps) = 1fs.
  // Even though the last `timescale has 1ps, the earlier 1fs wins.
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);
}

TEST(Preprocessor, DelayToTicks_Basic) {
  TimeScale ts;
  ts.unit = TimeUnit::kNs;
  ts.magnitude = 1;
  // 10 delay units at 1ns with 1ps precision = 10,000 ticks.
  EXPECT_EQ(DelayToTicks(10, ts, TimeUnit::kPs), 10000);
}

}  // namespace
