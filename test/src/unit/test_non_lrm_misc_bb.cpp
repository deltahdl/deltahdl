// Non-LRM tests

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

// 20. Global precision considers timeunit precision argument (slash syntax).
TEST(ParserClause03, Cl3_14_3_ConsidersTimeunitPrecArg) {
  auto r = ParseTimescale31402(
      "module a;\n"
      "  timeunit 1us / 1fs;\n"
      "endmodule\n"
      "module b;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);  // min of fs, ns = fs
}

}  // namespace
