#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult2214 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult2214 Parse(const std::string &src) {
  ParseResult2214 result;
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

// ============================================================================
// LRM section 22.14 -- `begin_keywords, `end_keywords
// ============================================================================

TEST(ParserSection22, BeginKeywords1800_2023) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2023\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1800_2017) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2017\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1800_2012) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2012\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1800_2009) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2009\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1800_2005) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2005\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1364_2005) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1364-2005\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1364_2001) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1364-2001\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1364_2001_noconfig) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1364-2001-noconfig\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1364_1995) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1364-1995\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywordsWithModuleContent) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2017\"\n"
              "module t;\n"
              "  logic [7:0] data;\n"
              "  initial data = 8'hFF;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywordsMultipleModules) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2012\"\n"
              "module m1;\n"
              "endmodule\n"
              "module m2;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, ModuleWithoutBeginKeywords) {
  auto r = Parse(
      "module m1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m1");
}

// ============================================================================
// AST-level checks for `begin_keywords
// ============================================================================

TEST(ParserSection22, BeginKeywordsModuleNamePreserved) {
  auto r = Parse(
      "`begin_keywords \"1800-2017\"\n"
      "module bar;\n"
      "  logic x;\n"
      "endmodule\n"
      "`end_keywords\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "bar");
}
