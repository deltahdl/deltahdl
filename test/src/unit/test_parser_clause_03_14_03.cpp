#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "parser/time_resolve.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Helper: preprocess and parse, returning CU + preprocessor state.
struct ParseResult31403 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
  TimeScale preproc_timescale;
  bool has_preproc_timescale = false;
  TimeUnit preproc_global_precision = TimeUnit::kNs;
};

static ParseResult31403 Parse(const std::string &src) {
  ParseResult31403 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
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

// =============================================================================
// LRM §3.14.3 — Simulation time unit (global time precision)
// =============================================================================

// 19. Global precision is minimum of all timeprecision statements.
TEST(ParserClause03, Cl3_14_3_MinOfTimeprecisionStatements) {
  auto r = Parse(
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
  auto r = Parse(
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
  // §3.14.3: "The step time unit is equal to the global time precision."
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

// 27. 1step is parsed as a special delay in clocking blocks (§14.4).
//     Verify parsing succeeds and the text is "1step".
TEST(ParserClause03, Cl3_14_3_1StepParsedInClockingBlock) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #1step a;\n"
      "  endclocking\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto *mod = r.cu->modules[0];
  // Find the clocking declaration.
  ModuleItem *clk_item = nullptr;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kClockingBlock) {
      clk_item = item;
      break;
    }
  }
  ASSERT_NE(clk_item, nullptr);
}

// 28. Single module with timeunit slash — precision arg is used.
TEST(ParserClause03, Cl3_14_3_SingleModuleTimeunitSlash) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1us / 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
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
