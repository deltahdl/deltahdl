// §3.14.2: Specifying time units and precision

#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"

using namespace delta;

// Helper: preprocess and parse, returning CU + preprocessor state.
struct ParseResult3140203 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
  TimeScale preproc_timescale;
  bool has_preproc_timescale = false;
  TimeUnit preproc_global_precision = TimeUnit::kNs;
};

static ParseResult3140203 ParseTimescale31402(const std::string& src) {
  ParseResult3140203 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.PreprocessTimescale(fid);
  result.preproc_timescale = preproc.CurrentTimescale();
  result.has_preproc_timescale = preproc.HasTimescale();
  result.preproc_global_precision = preproc.GlobalPrecision();
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// 30. Equivalent specifications: both mechanisms specify the same time values.
// `timescale 1ns/1ps is equivalent to timeunit 1ns; timeprecision 1ps.
TEST(ParserClause03, Cl3_14_2_EquivalentSpecifications) {
  // Way 1: `timescale directive.
  auto pp = PreprocessTimescale("`timescale 1ns / 1ps\n");
  EXPECT_FALSE(pp.has_errors);
  // Way 2: keywords inside a module.
  auto pr = ParseTimescale31402(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(pr.has_errors);
  // Both specify the same unit and precision.
  EXPECT_EQ(pp.timescale.unit, pr.cu->modules[0]->time_unit);
  EXPECT_EQ(pp.timescale.precision, pr.cu->modules[0]->time_prec);
}

}  // namespace
