#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "fixture_preprocessor.h"
#include "helpers_parser_verify.h"

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

TEST(Preprocessor, IfdefExprImplicationVacuous) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef (A -> B)\n"
      "vacuous\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("vacuous"), std::string::npos);
}

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

TEST(Preprocessor, IfdefExprEquivalenceBothUndef) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef (A <-> B)\n"
      "equiv_true\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("equiv_true"), std::string::npos);
}

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

TEST(Preprocessor, IfdefDirectiveNameNotDefined) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef ifdef\n"
      "should_not_appear\n"
      "`endif\n",
      f);
  EXPECT_EQ(result.find("should_not_appear"), std::string::npos);
}

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

TEST(Preprocessor, InlineIfdefTrue) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"FOO", "1"}};
  auto result = Preprocess("initial if (`ifdef FOO 1 `else 0 `endif)\n", f,
                           std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("initial if ( 1 )"), std::string::npos);
  EXPECT_EQ(result.find("`ifdef"), std::string::npos);
}

TEST(Preprocessor, InlineIfdefFalse) {
  PreprocFixture f;
  auto result = Preprocess("initial if (`ifdef FOO 1 `else 0 `endif)\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("initial if ( 0 )"), std::string::npos);
}

TEST(Preprocessor, InlineIfdefWithoutElse) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"FOO", "1"}};
  auto result =
      Preprocess("int x = `ifdef FOO 42 `endif;\n", f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
}

TEST(Preprocessor, InlineIfndefTrue) {
  PreprocFixture f;
  auto result = Preprocess("int x = `ifndef FOO 42 `else 0 `endif;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
}

TEST(Preprocessor, InlineIfdefExprForm) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}, {"B", "1"}};
  auto result = Preprocess("int x = `ifdef (A && B) 1 `else 0 `endif;\n", f,
                           std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find('1'), std::string::npos);
}

TEST(Preprocessor, InlineIfdefNested) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result =
      Preprocess("int x = `ifdef A `ifdef B 2 `else 1 `endif `else 0 `endif;\n",
                 f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find('1'), std::string::npos);
}

TEST(Preprocessor, DeeplyNestedIfdef) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"wow", ""}, {"nest_one", ""}, {"nest_two", ""}};
  auto result = Preprocess(
      "`ifdef wow\n"
      "wow_defined\n"
      "`ifdef nest_one\n"
      "nest_one_defined\n"
      "`ifdef nest_two\n"
      "nest_two_defined\n"
      "`else\n"
      "nest_two_undef\n"
      "`endif\n"
      "`else\n"
      "nest_one_undef\n"
      "`endif\n"
      "`else\n"
      "wow_undef\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("wow_defined"), std::string::npos);
  EXPECT_NE(result.find("nest_one_defined"), std::string::npos);
  EXPECT_NE(result.find("nest_two_defined"), std::string::npos);
  EXPECT_EQ(result.find("nest_two_undef"), std::string::npos);
  EXPECT_EQ(result.find("nest_one_undef"), std::string::npos);
  EXPECT_EQ(result.find("wow_undef"), std::string::npos);
}

TEST(Preprocessor, ChainedElsifWithNested) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"second_block", ""}};
  auto result = Preprocess(
      "`ifdef first_block\n"
      "first_block_text\n"
      "`elsif second_block\n"
      "second_block_text\n"
      "`else\n"
      "else_text\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_EQ(result.find("first_block_text"), std::string::npos);
  EXPECT_NE(result.find("second_block_text"), std::string::npos);
  EXPECT_EQ(result.find("else_text"), std::string::npos);
}

TEST(Preprocessor, ChainedElsifWithNestedIfndef) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"first_block", ""}, {"second_nest", ""}};
  auto result = Preprocess(
      "`ifdef first_block\n"
      "`ifndef second_nest\n"
      "first_only\n"
      "`else\n"
      "first_and_second\n"
      "`endif\n"
      "`else\n"
      "not_first\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_EQ(result.find("first_only"), std::string::npos);
  EXPECT_NE(result.find("first_and_second"), std::string::npos);
  EXPECT_EQ(result.find("not_first"), std::string::npos);
}

TEST(Preprocessor, EndifWithoutIfdef) {
  PreprocFixture f;
  Preprocess("`endif\n", f);

  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, ElseWithoutIfdef) {
  PreprocFixture f;
  Preprocess("`else\ntext\n`endif\n", f);

  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, IfdefWithoutEndif) {
  PreprocFixture f;
  Preprocess("`ifdef SOMETHING\ntext\n", f);

  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, IfdefEmptyBlocks) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`ifdef A\n"
      "`else\n"
      "else_text\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_EQ(result.find("else_text"), std::string::npos);
}

TEST(Preprocessor, IfdefAllEmptyBlocks) {
  PreprocFixture f;
  Preprocess(
      "`ifdef UNDEF\n"
      "`elsif ALSO_UNDEF\n"
      "`else\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, IfndefSimpleUndefined) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifndef UNDEF\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("visible"), std::string::npos);
}

TEST(Preprocessor, IfndefSimpleDefined) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"DEFINED", "1"}};
  auto result = Preprocess(
      "`ifndef DEFINED\n"
      "visible\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

TEST(Preprocessor, IfdefMacroDefinedToZero) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ZERO 0\n"
      "`ifdef ZERO\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("visible"), std::string::npos);
}

TEST(Preprocessor, IfdefMacroDefinedEmpty) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define EMPTY\n"
      "`ifdef EMPTY\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("visible"), std::string::npos);
}

TEST(CompilerDirectiveParsing, IfdefSelectsCorrectModule) {
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

TEST(CompilerDirectiveParsing, IfndefSelectsElseBranch) {
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
TEST(Preprocessor, Pragma_InsideIfdef_Inactive) {
  PreprocFixture f;
  Preprocess("`ifdef UNDEF_FLAG\n`pragma some_pragma\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IfdefConditionalCompilation, DefinedMacroTakesTrueBranch) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define HAS_MODULE\n"
      "`ifdef HAS_MODULE\n"
      "module m; endmodule\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module"), std::string::npos);
}

TEST(DesignElementPreprocessing, IfdefAroundModuleExcludesUntaken) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef UNDEFINED_MACRO\n"
      "module m; endmodule\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("module"), std::string::npos);
}

TEST(IfdefElse, UndefinedMacroSelectsElseBranch) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef MISSING\n"
      "module a; endmodule\n"
      "`else\n"
      "module b; endmodule\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("module a"), std::string::npos);
  EXPECT_NE(result.find("module b"), std::string::npos);
}

TEST(IfdefConditionalCompilation, MultipleDesignElementsWithConditional) {
  PreprocFixture f;
  auto result = Preprocess(
      "module always_present; endmodule\n"
      "`define INCLUDE_PKG\n"
      "`ifdef INCLUDE_PKG\n"
      "package pkg; endpackage\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("always_present"), std::string::npos);
  EXPECT_NE(result.find("package"), std::string::npos);
}

TEST(DesignElementPreprocessing, NestedIfdefAroundDesignElements) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define OUTER\n"
      "`define INNER\n"
      "`ifdef OUTER\n"
      "`ifdef INNER\n"
      "program p; endprogram\n"
      "`endif\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("program"), std::string::npos);
}

TEST(DesignElementPreprocessing, ElsifChainSelectsCorrectDesignElement) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define USE_IFACE\n"
      "`ifdef USE_MODULE\n"
      "module m; endmodule\n"
      "`elsif USE_IFACE\n"
      "interface ifc; endinterface\n"
      "`else\n"
      "package p; endpackage\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("module"), std::string::npos);
  EXPECT_NE(result.find("interface"), std::string::npos);
  EXPECT_EQ(result.find("package"), std::string::npos);
}

TEST(DesignElementPreprocessing, EmptyIfdefBodyPreservesSubsequent) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef UNDEFINED_MACRO\n"
      "`endif\n"
      "module m; endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module"), std::string::npos);
}

TEST(ConditionalCompilation, IfdefUndefinedExcludesBlock) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, y;\n"
      "`ifdef INCLUDE_GATE\n"
      "  and g1(y, a, b);\n"
      "`endif\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd), nullptr);
}

// A directive inside a multi-line block comment within a skipped block_of_text
// is hidden and must not terminate the surrounding conditional construct.
TEST(Preprocessor, BlockCommentInSkippedBlockHidesEndif) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef UNDEF_MACRO\n"
      "/* comment opens here\n"
      "`endif\n"
      "still inside comment */\n"
      "leaked_text\n"
      "`endif\n"
      "tail_text\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("leaked_text"), std::string::npos);
  EXPECT_NE(result.find("tail_text"), std::string::npos);
}

// The same hiding rule applies to a comment inside an active block_of_text: the
// commented `endif must not close the construct early.
TEST(Preprocessor, BlockCommentInActiveBlockHidesEndif) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"ON", "1"}};
  auto result = Preprocess(
      "`ifdef ON\n"
      "kept_text\n"
      "/* comment opens here\n"
      "`endif\n"
      "still inside comment */\n"
      "more_kept\n"
      "`endif\n"
      "after_text\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("kept_text"), std::string::npos);
  EXPECT_NE(result.find("more_kept"), std::string::npos);
  EXPECT_NE(result.find("after_text"), std::string::npos);
}

// Compiler directive names are not considered defined by `elsif (companion to
// the `ifdef case), so a `elsif naming a directive never selects its branch.
TEST(Preprocessor, ElsifDirectiveNameNotDefined) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef A\n"
      "branch_a\n"
      "`elsif endif\n"
      "should_not_appear\n"
      "`endif\n",
      f);
  EXPECT_EQ(result.find("branch_a"), std::string::npos);
  EXPECT_EQ(result.find("should_not_appear"), std::string::npos);
}

// A directive token appearing inside a text macro definition body is hidden and
// must not terminate the surrounding conditional construct. Here the `endif in
// the macro body must not close the `ifdef, so the `else branch stays skipped.
TEST(Preprocessor, DirectiveInMacroBodyHidesEndif) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"ON", "1"}};
  auto result = Preprocess(
      "`ifdef ON\n"
      "`define M `endif\n"
      "in_then\n"
      "`else\n"
      "in_else\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("in_then"), std::string::npos);
  EXPECT_EQ(result.find("in_else"), std::string::npos);
}

// A directive token appearing inside a string literal is hidden and must not be
// acted upon: the `else inside the string does not flip the active branch, so
// the text that follows in the taken branch is still emitted.
TEST(Preprocessor, DirectiveInStringLiteralHidesElse) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"ON", "1"}};
  auto result = Preprocess(
      "`ifdef ON\n"
      "initial $display(\"`else\");\n"
      "in_then\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("in_then"), std::string::npos);
  EXPECT_NE(result.find("`else"), std::string::npos);
}

// White space is not significant around the directives beyond separating
// tokens: leading indentation and extra spaces between a directive and its
// identifier are accepted and do not affect block selection or termination.
TEST(Preprocessor, IndentedAndSpacedDirectives) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "   `ifdef    A\n"
      "indented_then\n"
      "  `else\n"
      "indented_else\n"
      "   `endif\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("indented_then"), std::string::npos);
  EXPECT_EQ(result.find("indented_else"), std::string::npos);
}

// The hiding rule covers single-line comments too: a directive token after //
// is part of the comment, so a commented `else does not split the block and the
// text that follows stays in the (taken) then-branch.
TEST(Preprocessor, DirectiveInLineCommentHidesElse) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"ON", "1"}};
  auto result = Preprocess(
      "`ifdef ON\n"
      "then_text\n"
      "// `else\n"
      "still_then\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("then_text"), std::string::npos);
  EXPECT_NE(result.find("still_then"), std::string::npos);
}

// In a skipped block a `endif hidden behind // must not terminate the
// construct, so the surrounding conditional runs to its real `endif and the
// text in between remains excluded while text after the real `endif is emitted.
TEST(Preprocessor, LineCommentEndifInSkippedBlockDoesNotTerminate) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef UNDEF_MACRO\n"
      "skipped_text\n"
      "// `endif\n"
      "still_skipped\n"
      "`endif\n"
      "tail_text\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("skipped_text"), std::string::npos);
  EXPECT_EQ(result.find("still_skipped"), std::string::npos);
  EXPECT_NE(result.find("tail_text"), std::string::npos);
}

// An inline `ifdef ... `endif sequence that appears inside a string literal is
// hidden: it must be emitted verbatim, not evaluated as a conditional.
TEST(Preprocessor, InlineConditionalInsideStringIsHidden) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"ON", "1"}};
  auto result = Preprocess(
      "`ifdef ON\n"
      "initial $display(\"`ifdef NOPE 1 `endif kept\");\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("`ifdef NOPE 1 `endif kept"), std::string::npos);
}
