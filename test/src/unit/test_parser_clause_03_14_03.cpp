// §3.14.3: Simulation time unit

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

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

namespace {

// 21. Global precision considers `timescale precision.
TEST(ParserClause03, Cl3_14_3_ConsidersTimescalePrec) {
  auto r = Parse(
      "`timescale 1ns / 1ps\n"
      "module a;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);  // min of ns, ps = ps
}

// 22. Global precision across all three sources: timeprecision, timeunit
//     precision arg, and `timescale.
TEST(ParserClause03, Cl3_14_3_MinAcrossAllThreeSources) {
  auto r = Parse(
      "`timescale 1us / 1ns\n"
      "module a;\n"
      "  timeunit 1ms / 1us;\n"
      "endmodule\n"
      "module b;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);  // min of ns(`ts), us(tu/), ps(tp) = ps
}

// 23. With no time declarations, default is implementation-specific (kNs).
TEST(ParserClause03, Cl3_14_3_DefaultWhenNoneSpecified) {
  auto r = Parse(
      "module a;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kNs);  // default
}

// 24. Step time unit equals global time precision.
TEST(ParserClause03, Cl3_14_3_StepEqualsGlobalPrecision) {
  auto r = Parse(
      "module a;\n"
      "  timeprecision 1fs;\n"
      "endmodule\n"
      "module b;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);

  EXPECT_EQ(gp, TimeUnit::kFs);
}

}  // namespace
