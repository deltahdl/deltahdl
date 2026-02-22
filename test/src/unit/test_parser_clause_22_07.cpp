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
