#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "fixture_preprocessor.h"

using namespace delta;

TEST(Preprocessor, ElsifTakesSecondBranch) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"B", "1"}};
  auto result = Preprocess(
      "`ifdef A\n"
      "line_a\n"
      "`elsif B\n"
      "line_b\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("line_b"), std::string::npos);
  EXPECT_EQ(result.find("line_a"), std::string::npos);
}

TEST(Preprocessor, ElsifSkippedWhenFirstTaken) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}, {"B", "1"}};
  auto result = Preprocess(
      "`ifdef A\n"
      "line_a\n"
      "`elsif B\n"
      "line_b\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("line_a"), std::string::npos);
  EXPECT_EQ(result.find("line_b"), std::string::npos);
}

TEST(Preprocessor, ElsifElseFallthrough) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef A\n"
      "line_a\n"
      "`elsif B\n"
      "line_b\n"
      "`else\n"
      "line_else\n"
      "`endif\n",
      f);
  EXPECT_EQ(result.find("line_a"), std::string::npos);
  EXPECT_EQ(result.find("line_b"), std::string::npos);
  EXPECT_NE(result.find("line_else"), std::string::npos);
}

TEST(Preprocessor, MultipleElsif) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"C", "1"}};
  auto result = Preprocess(
      "`ifdef A\n"
      "line_a\n"
      "`elsif B\n"
      "line_b\n"
      "`elsif C\n"
      "line_c\n"
      "`else\n"
      "line_else\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_EQ(result.find("line_a"), std::string::npos);
  EXPECT_EQ(result.find("line_b"), std::string::npos);
  EXPECT_NE(result.find("line_c"), std::string::npos);
  EXPECT_EQ(result.find("line_else"), std::string::npos);
}

TEST(Preprocessor, NestedIfdefInsideElsif) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"B", "1"}, {"INNER", "1"}};
  auto result = Preprocess(
      "`ifdef A\n"
      "line_a\n"
      "`elsif B\n"
      "`ifdef INNER\n"
      "line_inner\n"
      "`endif\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("line_inner"), std::string::npos);
  EXPECT_EQ(result.find("line_a"), std::string::npos);
}

TEST(Preprocessor, IfdefElseRegression) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`ifdef A\n"
      "line_a\n"
      "`else\n"
      "line_else\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("line_a"), std::string::npos);
  EXPECT_EQ(result.find("line_else"), std::string::npos);
}

TEST(Preprocessor, IfdefExprAnd) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}, {"B", "1"}};
  auto result = Preprocess(
      "`ifdef (A && B)\n"
      "both_defined\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("both_defined"), std::string::npos);
}

TEST(Preprocessor, IfdefExprAndFalse) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`ifdef (A && B)\n"
      "both_defined\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_EQ(result.find("both_defined"), std::string::npos);
}

TEST(Preprocessor, IfdefExprOr) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`ifdef (A || B)\n"
      "either_defined\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("either_defined"), std::string::npos);
}

TEST(Preprocessor, IfdefExprNot) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef (!A)\n"
      "not_defined\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("not_defined"), std::string::npos);
}

TEST(Preprocessor, IfdefExprComplex) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`ifdef (A && (B || !C))\n"
      "complex_true\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("complex_true"), std::string::npos);
}
// §22.6: implication operator -> in ifdef expression.
// A -> B is equivalent to !A || B.
TEST(Preprocessor, IfdefExprImplication) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}, {"B", "1"}};
  auto result = Preprocess(
      "`ifdef (A -> B)\n"
      "impl_true\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("impl_true"), std::string::npos);
}

// §22.6: A -> B when A is true and B is false should be false.
TEST(Preprocessor, IfdefExprImplicationFalse) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`ifdef (A -> B)\n"
      "impl_true\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_EQ(result.find("impl_true"), std::string::npos);
}

// §22.6: A -> B when A is false should be true (vacuously).
TEST(Preprocessor, IfdefExprImplicationVacuous) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef (A -> B)\n"
      "vacuous\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("vacuous"), std::string::npos);
}

// §22.6: equivalence operator <-> in ifdef expression.
// A <-> B is true when both are defined or both are undefined.
TEST(Preprocessor, IfdefExprEquivalence) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}, {"B", "1"}};
  auto result = Preprocess(
      "`ifdef (A <-> B)\n"
      "equiv_true\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("equiv_true"), std::string::npos);
}

// §22.6: A <-> B when only A is defined should be false.
TEST(Preprocessor, IfdefExprEquivalenceFalse) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`ifdef (A <-> B)\n"
      "equiv_true\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_EQ(result.find("equiv_true"), std::string::npos);
}

// §22.6: A <-> B when both are undefined should be true.
TEST(Preprocessor, IfdefExprEquivalenceBothUndef) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef (A <-> B)\n"
      "equiv_true\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("equiv_true"), std::string::npos);
}

// §22.6: `ifndef (expr) is treated as `ifdef (!(expr)).
TEST(Preprocessor, IfndefExprForm) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`ifndef (A && B)\n"
      "ifndef_expr\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("ifndef_expr"), std::string::npos);
}

// §22.6: `ifndef (expr) when expr is true should exclude block.
TEST(Preprocessor, IfndefExprFormTrue) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}, {"B", "1"}};
  auto result = Preprocess(
      "`ifndef (A && B)\n"
      "ifndef_expr\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_EQ(result.find("ifndef_expr"), std::string::npos);
}

// §22.6: compiler directive names are not considered defined by `ifdef.
TEST(Preprocessor, IfdefDirectiveNameNotDefined) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef ifdef\n"
      "should_not_appear\n"
      "`endif\n",
      f);
  EXPECT_EQ(result.find("should_not_appear"), std::string::npos);
}

// §22.6: `elsif with expression form.
TEST(Preprocessor, ElsifExprForm) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"B", "1"}, {"C", "1"}};
  auto result = Preprocess(
      "`ifdef A\n"
      "line_a\n"
      "`elsif (B && C)\n"
      "line_bc\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("line_bc"), std::string::npos);
}

// §22.6: nested ifdef in skipped branch does not affect outer.
TEST(Preprocessor, NestedIfdefInSkippedBranch) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef UNDEF\n"
      "`ifdef ALSO_UNDEF\n"
      "inner\n"
      "`else\n"
      "inner_else\n"
      "`endif\n"
      "`else\n"
      "outer_else\n"
      "`endif\n",
      f);
  EXPECT_EQ(result.find("inner"), std::string::npos);
  EXPECT_NE(result.find("outer_else"), std::string::npos);
}

// §22.6: `ifdef with `define inside a taken branch.
TEST(Preprocessor, IfdefDefineInTakenBranch) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"FEATURE", "1"}};
  auto result = Preprocess(
      "`ifdef FEATURE\n"
      "`define INNER_MAC value\n"
      "`endif\n"
      "`ifdef INNER_MAC\n"
      "inner_visible\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("inner_visible"), std::string::npos);
}

// §22.6: `define inside a skipped branch should not be defined.
TEST(Preprocessor, DefineInSkippedBranchNotDefined) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef UNDEF\n"
      "`define SKIP_MAC value\n"
      "`endif\n"
      "`ifdef SKIP_MAC\n"
      "skip_visible\n"
      "`endif\n",
      f);
  EXPECT_EQ(result.find("skip_visible"), std::string::npos);
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
