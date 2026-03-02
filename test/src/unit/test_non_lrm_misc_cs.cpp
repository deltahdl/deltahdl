// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, DumpvarsInsideBeginEnd) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    $dumpfile(\"test.vcd\");\n"
      "    $dumpvars(0, t);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_GE(item->body->stmts.size(), 2u);
}

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

// 31. Text macro name space (d) — `define introduces names with leading `
TEST(ParserClause03, Cl3_13_TextMacroNameSpace) {
  // Macro defined and used; subsequent redefinition overrides previous
  auto r = Parse(
      "`define WIDTH 8\n"
      "`define DEPTH 16\n"
      "module m;\n"
      "  logic [`WIDTH-1:0] data;\n"
      "  logic [`DEPTH-1:0] addr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  // Macro names are unambiguous with other name spaces (leading ` character)
  EXPECT_TRUE(
      ParseOk("`define data 42\n"
              "module m; logic [7:0] data; endmodule\n"));
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
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
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
  auto r = ParseWithPreprocessor(
      "`timescale 1ns/1ps\n"
      "module foo;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "foo");
}

// 35. LRM example: three modules A, B, C with two `timescale directives.
// §3.14.2.1:
// `timescale 1ns / 10ps → modules A and B
// `timescale 1ps / 1ps  → module C
TEST(ParserClause03, Cl3_14_2_1_LrmExampleThreeModules) {
  auto r = ParseWithPreprocessor(
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
// AST-level checks for `default_nettype
// ============================================================================
TEST(ParserSection22, DefaultNettypeModuleCount) {
  auto r = ParseWithPreprocessor(
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

TEST(ParserSection22, CelldefineEndcelldefine) {
  EXPECT_TRUE(
      ParseOk("`celldefine\n"
              "module inv(output y, input a);\n"
              "  assign y = ~a;\n"
              "endmodule\n"
              "`endcelldefine\n"));
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

}  // namespace
