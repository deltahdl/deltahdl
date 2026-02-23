// §3.14: Simulation time units and precision

#include <gtest/gtest.h>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Helper: preprocess source and return timescale state.
struct PreprocResult3140201 {
  SourceManager mgr;
  TimeScale timescale;
  TimeUnit global_precision;
  bool has_timescale;
  bool has_errors;
};

static PreprocResult3140201 Preprocess(const std::string &src) {
  PreprocResult3140201 result;
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
struct ParseResult3140201 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult3140201 Parse(const std::string &src) {
  ParseResult3140201 result;
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

namespace {

// 38. Global precision tracks the finest precision across all `timescale
// directives.  This is necessary for delay conversion (§3.14.1).
TEST(ParserClause03, Cl3_14_2_1_GlobalPrecisionTracking) {
  // Two directives: 1ns/1ps then 1us/1ns.
  // Global precision should be the finer one: 1ps.
  auto r = Preprocess(
      "`timescale 1ns / 1ps\n"
      "`timescale 1us / 1ns\n");
  EXPECT_FALSE(r.has_errors);
  // Current timescale is the last one.
  EXPECT_EQ(r.timescale.precision, TimeUnit::kNs);
  // Global precision is the finest across all directives.
  EXPECT_EQ(r.global_precision, TimeUnit::kPs);
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
