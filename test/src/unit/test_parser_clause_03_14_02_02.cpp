// §3.14.2.2: The timeunit and timeprecision keywords

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

struct ParseResult23b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult23b Parse(const std::string& src) {
  ParseResult23b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// --- timeunit / timeprecision (LRM section 3.14) ---
TEST(ParserSection23, TimeunitDecl) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  // timeunit is consumed; no items generated (just parsed and skipped).
}

TEST(ParserSection23, TimeprecisionDecl) {
  auto r = Parse(
      "module m;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

TEST(ParserSection23, TimeunitAndTimeprecision) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 100ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

}  // namespace
