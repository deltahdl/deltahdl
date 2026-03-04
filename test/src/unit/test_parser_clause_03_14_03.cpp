// §3.14.3: Simulation time unit

#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_parser_verify.h"

using namespace delta;
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

// 25. CU-scope timeprecision is included in global computation.
TEST(ParserClause03, Cl3_14_3_CUScopeTimeprecisionIncluded) {
  auto r = Parse(
      "timeprecision 1fs;\n"
      "module a;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);  // CU-scope fs < module ns
}

// 26. Interfaces and programs also contribute to global precision.
TEST(ParserClause03, Cl3_14_3_InterfacesAndProgramsContribute) {
  auto r = Parse(
      "interface i;\n"
      "  timeprecision 1ps;\n"
      "endinterface\n"
      "program p;\n"
      "  timeprecision 1ns;\n"
      "endprogram\n"
      "module m;\n"
      "  timeprecision 1us;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);  // min of ps, ns, us = ps
}

// =============================================================================
// LRM §3.14.3 — Simulation time unit (global time precision)
// =============================================================================
// 19. Global precision is minimum of all timeprecision statements.
TEST(ParserClause03, Cl3_14_3_MinOfTimeprecisionStatements) {
  auto r = ParseTimescale31402(
      "module a;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n"
      "module b;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n"
      "module c;\n"
      "  timeprecision 1us;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);  // min of ns, ps, us = ps
}

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
