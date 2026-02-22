#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult2206 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult2206 Parse(const std::string &src) {
  ParseResult2206 result;
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

TEST(ParserSection22, IfdefDefined) {
  EXPECT_TRUE(
      ParseOk("`define FEATURE_A\n"
              "`ifdef FEATURE_A\n"
              "module t;\n"
              "endmodule\n"
              "`endif\n"));
}

TEST(ParserSection22, IfdefWithElse) {
  EXPECT_TRUE(
      ParseOk("`ifdef UNDEFINED_MACRO\n"
              "module alt;\n"
              "endmodule\n"
              "`else\n"
              "module t;\n"
              "endmodule\n"
              "`endif\n"));
}

TEST(ParserSection22, IfndefUndefined) {
  EXPECT_TRUE(
      ParseOk("`ifndef GUARD\n"
              "`define GUARD\n"
              "module t;\n"
              "endmodule\n"
              "`endif\n"));
}

TEST(ParserSection22, IfdefElsifChain) {
  EXPECT_TRUE(
      ParseOk("`define OPT_B\n"
              "`ifdef OPT_A\n"
              "module ma;\n"
              "endmodule\n"
              "`elsif OPT_B\n"
              "module mb;\n"
              "endmodule\n"
              "`else\n"
              "module mc;\n"
              "endmodule\n"
              "`endif\n"));
}

TEST(ParserSection22, NestedIfdef) {
  EXPECT_TRUE(
      ParseOk("`define OUTER\n"
              "`define INNER\n"
              "`ifdef OUTER\n"
              "`ifdef INNER\n"
              "module t;\n"
              "endmodule\n"
              "`endif\n"
              "`endif\n"));
}

TEST(ParserSection22, IfdefSelectsCorrectModule) {
  auto r = Parse(
      "`define USE_A\n"
      "`ifdef USE_A\n"
      "module a;\n"
      "endmodule\n"
      "`else\n"
      "module b;\n"
      "endmodule\n"
      "`endif\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
}

TEST(ParserSection22, IfndefSelectsElseBranch) {
  auto r = Parse(
      "`define GUARD\n"
      "`ifndef GUARD\n"
      "module unreachable;\n"
      "endmodule\n"
      "`else\n"
      "module reached;\n"
      "endmodule\n"
      "`endif\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "reached");
}
