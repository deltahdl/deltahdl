#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult2207 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult2207 Parse(const std::string &src) {
  ParseResult2207 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
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

TEST(ParserSection22, TimescaleNsPs) {
  EXPECT_TRUE(
      ParseOk("`timescale 1ns/1ps\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, Timescale10ns1ns) {
  EXPECT_TRUE(
      ParseOk("`timescale 10ns/1ns\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, Timescale100ns10ns) {
  EXPECT_TRUE(
      ParseOk("`timescale 100ns/10ns\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, TimescaleUsNs) {
  EXPECT_TRUE(
      ParseOk("`timescale 1us/1ns\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, TimescaleMsUs) {
  EXPECT_TRUE(
      ParseOk("`timescale 1ms/1us\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, MultipleTimescales) {
  EXPECT_TRUE(
      ParseOk("`timescale 1ns/1ps\n"
              "module m1;\n"
              "endmodule\n"
              "`timescale 10ns/1ns\n"
              "module m2;\n"
              "endmodule\n"));
}

TEST(ParserSection22, TimescaleWithDelays) {
  EXPECT_TRUE(
      ParseOk("`timescale 1ns/1ps\n"
              "module t;\n"
              "  reg clk;\n"
              "  initial begin\n"
              "    clk = 0;\n"
              "    #5 clk = 1;\n"
              "    #5 clk = 0;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection22, TimescaleModuleNamePreserved) {
  auto r = Parse(
      "`timescale 1ns/1ps\n"
      "module foo;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "foo");
}
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

// 35. LRM example: three modules A, B, C with two `timescale directives.
// §3.14.2.1:
// `timescale 1ns / 10ps → modules A and B
// `timescale 1ps / 1ps  → module C
TEST(ParserClause03, Cl3_14_2_1_LrmExampleThreeModules) {
  auto r = Parse(
      "`timescale 1ns / 10ps\n"
      "module A; endmodule\n"
      "module B; endmodule\n"
      "`timescale 1ps / 1ps\n"
      "module C; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 3u);
  // All three modules parse; none have explicit timeunit keywords.
  EXPECT_FALSE(r.cu->modules[0]->has_timeunit);
  EXPECT_FALSE(r.cu->modules[1]->has_timeunit);
  EXPECT_FALSE(r.cu->modules[2]->has_timeunit);
}

