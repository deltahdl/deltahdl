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
