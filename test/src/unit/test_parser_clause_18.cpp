#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §18 Constrained random — parsing
// =============================================================================

// --- Multi-declarator rand properties (§18.4) ---

TEST(ParserSection18, RandMultiDeclarator) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, c;\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_GE(r.cu->classes[0]->members.size(), 3u);
}

TEST(ParserSection18, RandcMultiDeclarator) {
  auto r = Parse(
      "class C;\n"
      "  randc bit [2:0] x, y;\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_GE(r.cu->classes[0]->members.size(), 2u);
}

// --- int unsigned return type and variable decl (§18.13) ---

TEST(ParserSection18, IntUnsignedFunctionReturnType) {
  auto r = Parse(
      "class C;\n"
      "  function int unsigned get_val();\n"
      "    int unsigned x;\n"
      "    x = 42;\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_GE(r.cu->classes[0]->members.size(), 1u);
}

// --- Extern constraint declaration (§18.5.1) ---

TEST(ParserSection18, ExternConstraintDecl) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c;\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, ImplicitExternConstraintDecl) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c;\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// --- Randcase statement (§18.16) ---

TEST(ParserSection18, RandcaseStmt) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : $display(\"one\");\n"
      "      2 : $display(\"two\");\n"
      "      3 : $display(\"three\");\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// --- Randsequence statement (§18.17) ---

TEST(ParserSection18, RandsequenceStmt) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : first second;\n"
      "      first : { $display(\"first\"); };\n"
      "      second : { $display(\"second\"); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// --- Top-level function declaration (§13) ---

TEST(ParserSection18, TopLevelFunction) {
  auto r = Parse(
      "function int my_func(int x);\n"
      "  return x + 1;\n"
      "endfunction\n"
      "class C;\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// --- Block-level var decl in function body ---

TEST(ParserSection18, FuncBodyVarDecl) {
  auto r = Parse(
      "module top;\n"
      "  function int foo();\n"
      "    int x;\n"
      "    x = 5;\n"
      "    return x;\n"
      "  endfunction\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// --- Out-of-block constraint declaration (§18.5.1) ---

TEST(ParserSection18, OutOfBlockConstraint) {
  auto r = Parse(
      "class a;\n"
      "  rand int b;\n"
      "  extern constraint c;\n"
      "endclass\n"
      "constraint a::c { b == 0; }\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// --- Inline randomize with constraint block (§18.7) ---

TEST(ParserSection18, RandomizeWithInlineConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void test();\n"
      "    this.randomize() with { x > 0; x < 100; };\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, RandomizeWithIdListAndConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  function void test();\n"
      "    this.randomize() with (x) { x > 0; x < y; };\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// --- Rand array property in class (§18.5.8.1) ---

TEST(ParserSection18, RandArrayInClass) {
  auto r = Parse(
      "class a;\n"
      "  rand int B[5];\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_GE(r.cu->classes[0]->members.size(), 1u);
}

TEST(ParserSection18, RandArrayInClassWithConstraint) {
  auto r = Parse(
      "class a;\n"
      "  rand int B[5];\n"
      "  constraint c { foreach (B[i]) B[i] == 5; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, StdRandomizeWithConstraint) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    int x;\n"
      "    std::randomize(x) with { x > 0; x < 10; };\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// =============================================================================
// §18.5.3 Distribution constraints
// =============================================================================

TEST(ParserSection18, DistConstraintEqualWeight) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100:=1, 200:=2, 300:=5}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, DistConstraintDivideWeight) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100:/1, 200:/2, 300:/5}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, DistConstraintWithRange) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[100:102]:=1, 103:=1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, DistConstraintWithDefault) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[100:102]:/3, default:/1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// =============================================================================
// §18.7 Inline constraints -- randomize() with (additional)
// =============================================================================

TEST(ParserSection18, RandomizeWithNullArg) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  function void test();\n"
      "    this.randomize(null) with { x > 0; };\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, RandomizeWithMultipleConstraints) {
  auto r = Parse(
      "class SimpleSum;\n"
      "  rand bit [7:0] x, y, z;\n"
      "  constraint c { z == x + y; }\n"
      "  function void test();\n"
      "    this.randomize() with { x < y; x > 10; y < 200; };\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, RandomizeWithRestrictedIdList) {
  auto r = Parse(
      "class C;\n"
      "  rand integer x;\n"
      "endclass\n"
      "function int F(int y);\n"
      "  C obj;\n"
      "  F = obj.randomize() with (x) { x < y; };\n"
      "endfunction\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, StdRandomizeWithMultipleVars) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    int x, y;\n"
      "    std::randomize(x, y) with { x + y < 100; x > 0; y > 0; };\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// =============================================================================
// §18.13.3 srandom() -- random stability and process
// =============================================================================

TEST(ParserSection18, SrandomMethodCall) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void seed_it();\n"
      "    this.srandom(42);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, SrandomInInitialBlock) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    process p;\n"
      "    p = process::self();\n"
      "    p.srandom(123);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection18, SrandomWithExpression) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void seed_it(int seed_val);\n"
      "    this.srandom(seed_val + 1);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// =============================================================================
// §18.13.4 get_randstate()
// =============================================================================

TEST(ParserSection18, GetRandstateCall) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function string save_state();\n"
      "    return this.get_randstate();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, GetRandstateAssignToVar) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    process p;\n"
      "    string state;\n"
      "    p = process::self();\n"
      "    state = p.get_randstate();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection18, GetRandstateInFunction) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void checkpoint(output string s);\n"
      "    s = this.get_randstate();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// =============================================================================
// §18.13.5 set_randstate()
// =============================================================================

TEST(ParserSection18, SetRandstateCall) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void restore_state(string state);\n"
      "    this.set_randstate(state);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, SetRandstateInInitialBlock) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    process p;\n"
      "    string saved;\n"
      "    p = process::self();\n"
      "    saved = p.get_randstate();\n"
      "    p.set_randstate(saved);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection18, GetSetRandstateRoundtrip) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void save_and_restore();\n"
      "    string s;\n"
      "    s = this.get_randstate();\n"
      "    this.randomize();\n"
      "    this.set_randstate(s);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}
