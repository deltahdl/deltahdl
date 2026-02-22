#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Helper: lex a single token from source text.
// Returns both the SourceManager (owning the source buffer) and the token
// so that token.text (a string_view) remains valid.
struct LexResult {
  SourceManager mgr;
  Token token;
};

static LexResult LexOne(const std::string &src) {
  LexResult result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  result.token = lexer.Next();
  return result;
}

// Helper: parse source and return the compilation unit.
struct ParseResult314 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult314 Parse(const std::string &src) {
  ParseResult314 result;
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

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// =============================================================================
// LRM §3.14 — Simulation time units and precision
// =============================================================================

TEST(ParserClause03, Cl3_14_TimeunitsAndTimescale) {
  auto r1 = Parse("module m; timeunit 1ns; endmodule\n");
  EXPECT_FALSE(r1.has_errors);
  EXPECT_TRUE(r1.cu->modules[0]->has_timeunit);
  auto r2 = Parse("module m; timeprecision 1ps; endmodule\n");
  EXPECT_FALSE(r2.has_errors);
  EXPECT_TRUE(r2.cu->modules[0]->has_timeprecision);
  auto r3 = Parse("module m; timeunit 1ns; timeprecision 1ps; endmodule\n");
  EXPECT_FALSE(r3.has_errors);
  EXPECT_TRUE(r3.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r3.cu->modules[0]->has_timeprecision);
  EXPECT_TRUE(ParseOk("module m; timeunit 100ps / 10fs; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("program p; timeunit 10us; timeprecision 100ns; endprogram\n"));
  EXPECT_TRUE(ParseOk("interface ifc; timeunit 1ns; endinterface\n"));
  // `timescale directive
  EXPECT_TRUE(ParseOk("`timescale 1ns/1ps\nmodule m; endmodule\n"));
  // Time literals (§5.8): integer, fractional, all unit suffixes
  EXPECT_TRUE(ParseOk("module m; initial #10ns $display(\"d\"); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m; initial #2.1ns $display(\"d\"); endmodule\n"));
  // Various magnitudes (Table 3-1)
  EXPECT_TRUE(
      ParseOk("module a; timeunit 100ns; timeprecision 10ps; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module b; timeunit 1us; timeprecision 1ns; endmodule\n"));
}

// 1. TimeUnit enum: six values with correct power-of-10 exponents
// (s=0, ms=-3, us=-6, ns=-9, ps=-12, fs=-15).
TEST(ParserClause03, Cl3_14_TimeUnitEnumValues) {
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kS), 0);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kMs), -3);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kUs), -6);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kNs), -9);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kPs), -12);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kFs), -15);
}

// 2. Table 3-1: ParseTimeUnitStr maps all six character strings.
TEST(ParserClause03, Cl3_14_Table3_1_AllUnitStrings) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_TRUE(ParseTimeUnitStr("s", u));
  EXPECT_EQ(u, TimeUnit::kS);
  EXPECT_TRUE(ParseTimeUnitStr("ms", u));
  EXPECT_EQ(u, TimeUnit::kMs);
  EXPECT_TRUE(ParseTimeUnitStr("us", u));
  EXPECT_EQ(u, TimeUnit::kUs);
  EXPECT_TRUE(ParseTimeUnitStr("ns", u));
  EXPECT_EQ(u, TimeUnit::kNs);
  EXPECT_TRUE(ParseTimeUnitStr("ps", u));
  EXPECT_EQ(u, TimeUnit::kPs);
  EXPECT_TRUE(ParseTimeUnitStr("fs", u));
  EXPECT_EQ(u, TimeUnit::kFs);
}

// 3. Table 3-1: invalid unit strings are rejected.
TEST(ParserClause03, Cl3_14_Table3_1_InvalidStrings) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_FALSE(ParseTimeUnitStr("", u));
  EXPECT_FALSE(ParseTimeUnitStr("xs", u));
  EXPECT_FALSE(ParseTimeUnitStr("sec", u));
  EXPECT_FALSE(ParseTimeUnitStr("NS", u)); // case-sensitive
}

// 4. "us" represents microseconds (substitution for the mu-s symbol).
TEST(ParserClause03, Cl3_14_UsForMicroseconds) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_TRUE(ParseTimeUnitStr("us", u));
  EXPECT_EQ(u, TimeUnit::kUs);
  EXPECT_EQ(static_cast<int8_t>(u), -6); // 10^-6 = microsecond
}

// 5. TimeScale struct: time values have two components (unit + precision).
TEST(ParserClause03, Cl3_14_TimeScaleTwoComponents) {
  TimeScale ts;
  ts.unit = TimeUnit::kNs;
  ts.magnitude = 1;
  ts.precision = TimeUnit::kPs;
  ts.prec_magnitude = 1;
  EXPECT_EQ(ts.unit, TimeUnit::kNs);
  EXPECT_EQ(ts.precision, TimeUnit::kPs);
  // Unit and precision are independently stored.
  EXPECT_NE(static_cast<int8_t>(ts.unit), static_cast<int8_t>(ts.precision));
}

// 6. Three orders of magnitude: 1, 10, 100.
// DelayToTicks produces proportionally different tick counts.
TEST(ParserClause03, Cl3_14_ThreeMagnitudes) {
  TimeScale ts1{TimeUnit::kNs, 1, TimeUnit::kPs, 1};
  TimeScale ts10{TimeUnit::kNs, 10, TimeUnit::kPs, 1};
  TimeScale ts100{TimeUnit::kNs, 100, TimeUnit::kPs, 1};
  EXPECT_EQ(DelayToTicks(1, ts1, TimeUnit::kPs), 1000u);
  EXPECT_EQ(DelayToTicks(1, ts10, TimeUnit::kPs), 10000u);
  EXPECT_EQ(DelayToTicks(1, ts100, TimeUnit::kPs), 100000u);
}

// 7. Lexer: all six time suffixes produce kTimeLiteral tokens.
TEST(ParserClause03, Cl3_14_LexerAllTimeSuffixes) {
  auto r_s = LexOne("1s");
  EXPECT_EQ(r_s.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_s.token.text, "1s");
  auto r_ms = LexOne("1ms");
  EXPECT_EQ(r_ms.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_ms.token.text, "1ms");
  auto r_us = LexOne("1us");
  EXPECT_EQ(r_us.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_us.token.text, "1us");
  auto r_ns = LexOne("1ns");
  EXPECT_EQ(r_ns.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_ns.token.text, "1ns");
  auto r_ps = LexOne("1ps");
  EXPECT_EQ(r_ps.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_ps.token.text, "1ps");
  auto r_fs = LexOne("1fs");
  EXPECT_EQ(r_fs.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_fs.token.text, "1fs");
}

// 8. Lexer: magnitudes 1, 10, 100 with time suffix.
TEST(ParserClause03, Cl3_14_LexerTimeMagnitudes) {
  auto r1 = LexOne("1ns");
  EXPECT_EQ(r1.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r1.token.text, "1ns");
  auto r10 = LexOne("10ns");
  EXPECT_EQ(r10.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r10.token.text, "10ns");
  auto r100 = LexOne("100ns");
  EXPECT_EQ(r100.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r100.token.text, "100ns");
}

// 9. SimTime: simulation time is maintained as ticks with comparison
// and addition operators.
TEST(ParserClause03, Cl3_14_SimTimeOperations) {
  SimTime t0{0};
  SimTime t1{1000};
  SimTime t2{1000};
  EXPECT_EQ(t0.ticks, 0u);
  EXPECT_EQ(t1.ticks, 1000u);
  EXPECT_TRUE(t0 < t1);
  EXPECT_TRUE(t0 <= t1);
  EXPECT_FALSE(t0 > t1);
  EXPECT_TRUE(t1 > t0);
  EXPECT_TRUE(t1 == t2);
  SimTime t3 = t0 + t1;
  EXPECT_EQ(t3.ticks, 1000u);
}

// 10. DelayToTicks: when unit == precision, delay maps 1:1 to ticks.
TEST(ParserClause03, Cl3_14_DelayToTicksSameUnit) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kNs, 1};
  EXPECT_EQ(DelayToTicks(42, ts, TimeUnit::kNs), 42u);
}

// 11. DelayToTicks covers the full range from seconds to femtoseconds.
TEST(ParserClause03, Cl3_14_DelayToTicksFullRange) {
  // 1 second at fs precision = 10^15 ticks.
  TimeScale ts_s{TimeUnit::kS, 1, TimeUnit::kFs, 1};
  EXPECT_EQ(DelayToTicks(1, ts_s, TimeUnit::kFs), 1000000000000000ULL);
  // 1 fs at fs precision = 1 tick.
  TimeScale ts_fs{TimeUnit::kFs, 1, TimeUnit::kFs, 1};
  EXPECT_EQ(DelayToTicks(1, ts_fs, TimeUnit::kFs), 1u);
}

// 12. Precision constraint: precision exponent <= unit exponent.
// Finer units have more-negative exponents (kFs < kPs < ... < kS).
TEST(ParserClause03, Cl3_14_PrecisionAtLeastAsPreciseAsUnit) {
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kFs),
            static_cast<int8_t>(TimeUnit::kPs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kPs),
            static_cast<int8_t>(TimeUnit::kNs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kNs),
            static_cast<int8_t>(TimeUnit::kUs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kUs),
            static_cast<int8_t>(TimeUnit::kMs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kMs),
            static_cast<int8_t>(TimeUnit::kS));
}

// 13. Time values stored in design element: module with timeunit and
// timeprecision stores both components.
TEST(ParserClause03, Cl3_14_TimeValuesInDesignElement) {
  auto r = Parse("module m;\n"
                 "  timeunit 1ns;\n"
                 "  timeprecision 1ps;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto *mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}
