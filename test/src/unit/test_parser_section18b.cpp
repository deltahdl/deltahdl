#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

struct ParseResult18b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult18b Parse(const std::string& src) {
  ParseResult18b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 18.5.3 -- Distribution constraints (additional tests)
// =============================================================================

TEST(ParserSection18b, DistEqualWeightSingleValue) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {42 := 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistDivideWeightMultipleValues) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {1 :/ 1, 2 :/ 1, 3 :/ 1, 4 :/ 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistWithRangeAndEqualWeight) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[0:3] := 1, [4:7] := 2}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistWithMixedWeightTypes) {
  // Mix of := and :/ in the same distribution
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {0 := 1, [1:10] :/ 5, 11 := 3}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistWithDefaultWeight) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[0:255] :/ 1, default :/ 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistInsideIfConstraint) {
  // Distribution inside a conditional constraint block
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand bit mode;\n"
      "  constraint c {\n"
      "    if (mode == 0) {\n"
      "      x dist {[0:10] := 1};\n"
      "    } else {\n"
      "      x dist {[100:200] := 1};\n"
      "    }\n"
      "  }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistWithExpressionWeights) {
  // Weights can be arbitrary constant expressions
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {1 := 2 * 3, 2 := 4 + 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistWithNegativeValues) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {-10 := 1, 0 := 2, 10 := 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistMultipleConstraints) {
  // Multiple dist constraints in one class
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  constraint cx { x dist {[0:100] := 1}; }\n"
      "  constraint cy { y dist {[0:50] :/ 2, [51:100] :/ 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}
