// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, FeofFerror) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, eof_flag;\n"
              "  reg [8*128:1] msg;\n"
              "  initial begin\n"
              "    fd = $fopen(\"data.txt\", \"r\");\n"
              "    eof_flag = $feof(fd);\n"
              "    $ferror(fd, msg);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpvarsLevelZeroAllHierarchy) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(0, top);\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpvarsMixedModulesAndVars) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(0, top.mod1, top.mod2.net1);\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpvarsInInitialBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpfile(\"module1.dump\");\n"
              "    $dumpvars(0, t);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, FullVcdWorkflow) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg clk;\n"
              "  initial begin\n"
              "    $dumpfile(\"dump1.dump\");\n"
              "    $dumpvars(0, t);\n"
              "    #10 $dumpoff;\n"
              "    #200 $dumpon;\n"
              "    #800 $dumpoff;\n"
              "  end\n"
              "endmodule\n"));
}

// ============================================================================
// Additional coverage -- Memory load/dump tasks from 21.1 overview
// ============================================================================
TEST(ParserSection21, ReadmemhBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemh(\"data.hex\", mem);\n"
              "endmodule\n"));
}

TEST(ParserSection21, ReadmemhWithAddresses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemh(\"data.hex\", mem, 0, 127);\n"
              "endmodule\n"));
}

TEST(ParserSection21, ReadmembBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemb(\"data.bin\", mem);\n"
              "endmodule\n"));
}

TEST(ParserSection21, ReadmembWithAddresses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $readmemb(\"data.bin\", mem, 16, 31);\n"
              "endmodule\n"));
}

TEST(ParserSection21, WritememhCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememh(\"out.hex\", mem);\n"
              "endmodule\n"));
}

TEST(ParserSection21, WritemembCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial $writememb(\"out.bin\", mem);\n"
              "endmodule\n"));
}

// ============================================================================
// Additional coverage -- Command line input from 21.1 overview
// ============================================================================
TEST(ParserSection21, TestPlusargsCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    if ($test$plusargs(\"VERBOSE\"))\n"
              "      $display(\"verbose mode\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, ValuePlusargsCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer depth;\n"
              "  initial begin\n"
              "    if ($value$plusargs(\"DEPTH=%d\", depth))\n"
              "      $display(\"depth=%0d\", depth);\n"
              "  end\n"
              "endmodule\n"));
}

// ============================================================================
// Additional coverage -- VCD port dump tasks from 21.1 overview
// ============================================================================
TEST(ParserSection21, DumpportsCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpports(t, \"ports.vcd\");\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpportsOffOnFlush) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $dumpports(t, \"ports.vcd\");\n"
              "    #100 $dumpportsoff;\n"
              "    #200 $dumpportson;\n"
              "    #300 $dumpportsflush;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpportslimitCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(500000);\n"
              "endmodule\n"));
}

// ============================================================================
// AST-level checks for system calls in initial blocks
// ============================================================================
TEST(ParserSection21, DisplayParsesAsSystemCall) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
}

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
