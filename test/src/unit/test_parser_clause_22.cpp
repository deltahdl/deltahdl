#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult22 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult22 Parse(const std::string& src) {
  ParseResult22 result;
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

static bool ParseOk(const std::string& src) {
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
// LRM section 22.1 -- General compiler directives overview
// ============================================================================

TEST(ParserSection22, ResetallDirective) {
  EXPECT_TRUE(
      ParseOk("`resetall\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, ResetallBeforeMultipleModules) {
  EXPECT_TRUE(
      ParseOk("`resetall\n"
              "module m1;\n"
              "endmodule\n"
              "module m2;\n"
              "endmodule\n"));
}

TEST(ParserSection22, CelldefineEndcelldefine) {
  EXPECT_TRUE(
      ParseOk("`celldefine\n"
              "module inv(output y, input a);\n"
              "  assign y = ~a;\n"
              "endmodule\n"
              "`endcelldefine\n"));
}

TEST(ParserSection22, UnconnectedDrivePull1) {
  EXPECT_TRUE(
      ParseOk("`unconnected_drive pull1\n"
              "module t;\n"
              "endmodule\n"
              "`nounconnected_drive\n"));
}

TEST(ParserSection22, UnconnectedDrivePull0) {
  EXPECT_TRUE(
      ParseOk("`unconnected_drive pull0\n"
              "module t;\n"
              "endmodule\n"
              "`nounconnected_drive\n"));
}

// ============================================================================
// LRM section 22.8 -- `default_nettype
// ============================================================================

TEST(ParserSection22, DefaultNettypeWire) {
  EXPECT_TRUE(
      ParseOk("`default_nettype wire\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeNone) {
  EXPECT_TRUE(
      ParseOk("`default_nettype none\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeTri) {
  EXPECT_TRUE(
      ParseOk("`default_nettype tri\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeWand) {
  EXPECT_TRUE(
      ParseOk("`default_nettype wand\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeWor) {
  EXPECT_TRUE(
      ParseOk("`default_nettype wor\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeTri0) {
  EXPECT_TRUE(
      ParseOk("`default_nettype tri0\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeTri1) {
  EXPECT_TRUE(
      ParseOk("`default_nettype tri1\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeTriand) {
  EXPECT_TRUE(
      ParseOk("`default_nettype triand\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeTrior) {
  EXPECT_TRUE(
      ParseOk("`default_nettype trior\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeTrireg) {
  EXPECT_TRUE(
      ParseOk("`default_nettype trireg\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeUwire) {
  EXPECT_TRUE(
      ParseOk("`default_nettype uwire\n"
              "module t;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefaultNettypeBeforeAndAfterModule) {
  EXPECT_TRUE(
      ParseOk("`default_nettype none\n"
              "module t;\n"
              "endmodule\n"
              "`default_nettype wire\n"));
}

TEST(ParserSection22, MultipleDefaultNettypeDirectives) {
  EXPECT_TRUE(
      ParseOk("`default_nettype wire\n"
              "module m1;\n"
              "endmodule\n"
              "`default_nettype none\n"
              "module m2;\n"
              "endmodule\n"));
}

// ============================================================================
// LRM section 22.13 -- `__FILE__ and `__LINE__
// ============================================================================

TEST(ParserSection22, FileDirectiveInDisplay) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"File: %s\", `__FILE__);\n"
              "endmodule\n"));
}

TEST(ParserSection22, LineDirectiveInDisplay) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"Line: %0d\", `__LINE__);\n"
              "endmodule\n"));
}

TEST(ParserSection22, FileAndLineInErrorMessage) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"Error at %s, line %d.\",\n"
              "    `__FILE__, `__LINE__);\n"
              "endmodule\n"));
}

TEST(ParserSection22, LineDirectiveInAssignment) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer line_num;\n"
              "  initial line_num = `__LINE__;\n"
              "endmodule\n"));
}

TEST(ParserSection22, FileDirectiveInStringConcat) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"source: %s:%0d\", `__FILE__, `__LINE__);\n"
              "endmodule\n"));
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
  // Without `begin_keywords, the default keyword set applies.
  auto r = Parse(
      "module m1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m1");
}

// ============================================================================
// Additional coverage -- `timescale (related to 22.1 general overview)
// ============================================================================

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

// ============================================================================
// Additional coverage -- `define and macro usage (related to 22.1 overview)
// ============================================================================

TEST(ParserSection22, DefineSimpleMacro) {
  EXPECT_TRUE(
      ParseOk("`define WIDTH 8\n"
              "module t;\n"
              "  logic [`WIDTH-1:0] data;\n"
              "endmodule\n"));
}

TEST(ParserSection22, DefineAndUndef) {
  EXPECT_TRUE(
      ParseOk("`define FOO 1\n"
              "module t;\n"
              "endmodule\n"
              "`undef FOO\n"));
}

TEST(ParserSection22, UndefineallDirective) {
  EXPECT_TRUE(
      ParseOk("`define A 1\n"
              "`define B 2\n"
              "`undefineall\n"
              "module t;\n"
              "endmodule\n"));
}

// ============================================================================
// Additional coverage -- `ifdef / `ifndef (related to 22.1 overview)
// ============================================================================

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

// ============================================================================
// AST-level checks for compiler directive interaction with modules
// ============================================================================

TEST(ParserSection22, TimescaleModuleNamePreserved) {
  auto r = Parse(
      "`timescale 1ns/1ps\n"
      "module foo;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "foo");
}

TEST(ParserSection22, DefaultNettypeModuleCount) {
  auto r = Parse(
      "`default_nettype wire\n"
      "module m1;\n"
      "endmodule\n"
      "`default_nettype none\n"
      "module m2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "m1");
  EXPECT_EQ(r.cu->modules[1]->name, "m2");
}

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
