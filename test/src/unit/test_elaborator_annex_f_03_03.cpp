#include <gtest/gtest.h>

#include "elaborator/annex_f_notation.h"

using namespace delta;

namespace {

// §F.3.3: b and c denote Boolean expressions.
TEST(NotationConventions, BooleanExpressionLetters) {
  EXPECT_EQ(ClassifyAnnexFNotation("b"), NotationCategory::kBooleanExpression);
  EXPECT_EQ(ClassifyAnnexFNotation("c"), NotationCategory::kBooleanExpression);
}

// §F.3.3: t denotes a type; v a local variable name; u a free checker
// variable name; e an expression. These are case-sensitive: t is a type,
// not the uppercase top-level-property letter T.
TEST(NotationConventions, TerminalLetters) {
  EXPECT_EQ(ClassifyAnnexFNotation("t"), NotationCategory::kType);
  EXPECT_EQ(ClassifyAnnexFNotation("v"), NotationCategory::kLocalVariableName);
  EXPECT_EQ(ClassifyAnnexFNotation("u"),
            NotationCategory::kFreeCheckerVariableName);
  EXPECT_EQ(ClassifyAnnexFNotation("e"), NotationCategory::kExpression);
}

// §F.3.3: uppercase R, S, P, Q, T, U denote, respectively, an unclocked
// sequence, clocked sequence, unclocked property, clocked property,
// unclocked top-level property, and clocked top-level property.
TEST(NotationConventions, UppercaseAbstractSyntaxLetters) {
  EXPECT_EQ(ClassifyAnnexFNotation("R"), NotationCategory::kUnclockedSequence);
  EXPECT_EQ(ClassifyAnnexFNotation("S"), NotationCategory::kClockedSequence);
  EXPECT_EQ(ClassifyAnnexFNotation("P"), NotationCategory::kUnclockedProperty);
  EXPECT_EQ(ClassifyAnnexFNotation("Q"), NotationCategory::kClockedProperty);
  EXPECT_EQ(ClassifyAnnexFNotation("T"),
            NotationCategory::kUnclockedTopLevelProperty);
  EXPECT_EQ(ClassifyAnnexFNotation("U"),
            NotationCategory::kClockedTopLevelProperty);
}

// §F.3.3: lowercase r and s denote sequences of either clock flavor.
TEST(NotationConventions, LowercaseSequenceLetters) {
  EXPECT_EQ(ClassifyAnnexFNotation("r"), NotationCategory::kSequence);
  EXPECT_EQ(ClassifyAnnexFNotation("s"), NotationCategory::kSequence);
  EXPECT_TRUE(DenotesSequence(NotationCategory::kSequence));
}

// §F.3.3: lowercase p and q denote properties, clocked or unclocked and
// top-level or not.
TEST(NotationConventions, LowercasePropertyLetters) {
  EXPECT_EQ(ClassifyAnnexFNotation("p"), NotationCategory::kProperty);
  EXPECT_EQ(ClassifyAnnexFNotation("q"), NotationCategory::kProperty);
  EXPECT_TRUE(DenotesProperty(NotationCategory::kProperty));
}

// §F.3.3: uppercase A denotes an assertion.
TEST(NotationConventions, AssertionLetter) {
  EXPECT_EQ(ClassifyAnnexFNotation("A"), NotationCategory::kAssertion);
}

// §F.3.3: i, j, k, m, and n denote non-negative integer constants.
TEST(NotationConventions, IntegerConstantLetters) {
  for (const char* sym : {"i", "j", "k", "m", "n"}) {
    EXPECT_EQ(ClassifyAnnexFNotation(sym),
              NotationCategory::kNonNegativeIntegerConstant)
        << "symbol: " << sym;
  }
}

// §F.3.3: the conventions distinguish case. A few representative letters
// carry different meanings in their two cases, and the model must not
// conflate them.
TEST(NotationConventions, CaseIsSignificant) {
  EXPECT_NE(ClassifyAnnexFNotation("r"), ClassifyAnnexFNotation("R"));
  EXPECT_NE(ClassifyAnnexFNotation("p"), ClassifyAnnexFNotation("P"));
  EXPECT_NE(ClassifyAnnexFNotation("q"), ClassifyAnnexFNotation("Q"));
  EXPECT_NE(ClassifyAnnexFNotation("s"), ClassifyAnnexFNotation("S"));
  // t is a type, T is an unclocked top-level property.
  EXPECT_NE(ClassifyAnnexFNotation("t"), ClassifyAnnexFNotation("T"));
  // u is a free checker variable, U is a clocked top-level property.
  EXPECT_NE(ClassifyAnnexFNotation("u"), ClassifyAnnexFNotation("U"));
}

// §F.3.3: the conventions cover subscripted versions of each notation, so
// a subscripted symbol resolves to the same category as its base letter.
TEST(NotationConventions, SubscriptedFormsShareBaseCategory) {
  EXPECT_EQ(ClassifyAnnexFNotation("b1"), NotationCategory::kBooleanExpression);
  EXPECT_EQ(ClassifyAnnexFNotation("e_1"), NotationCategory::kExpression);
  EXPECT_EQ(ClassifyAnnexFNotation("R2"), NotationCategory::kUnclockedSequence);
  EXPECT_EQ(ClassifyAnnexFNotation("R_2"),
            NotationCategory::kUnclockedSequence);
  EXPECT_EQ(ClassifyAnnexFNotation("n10"),
            NotationCategory::kNonNegativeIntegerConstant);
}

// §F.3.3 assigns no convention to letters it does not list (e.g. l, a, x)
// nor to multi-letter identifiers, so those resolve to no category.
TEST(NotationConventions, UnlistedSymbolsHaveNoConvention) {
  EXPECT_FALSE(ClassifyAnnexFNotation("l").has_value());
  EXPECT_FALSE(ClassifyAnnexFNotation("a").has_value());
  EXPECT_FALSE(ClassifyAnnexFNotation("x").has_value());
  EXPECT_FALSE(ClassifyAnnexFNotation("foo").has_value());
  EXPECT_FALSE(ClassifyAnnexFNotation("").has_value());
}

// §F.3.3: R, S, and the lowercase r/s all denote sequences (unclocked,
// clocked, or either-flavor). Every sequence-denoting category is
// recognized as a sequence, going through the classifier so the grouping
// is observed end to end.
TEST(NotationConventions, SequenceLettersAreSequences) {
  EXPECT_TRUE(DenotesSequence(NotationCategory::kUnclockedSequence));
  EXPECT_TRUE(DenotesSequence(NotationCategory::kClockedSequence));
  EXPECT_TRUE(DenotesSequence(NotationCategory::kSequence));
  for (const char* sym : {"R", "S", "r", "s"}) {
    auto category = ClassifyAnnexFNotation(sym);
    ASSERT_TRUE(category.has_value()) << "symbol: " << sym;
    EXPECT_TRUE(DenotesSequence(*category)) << "symbol: " << sym;
  }
}

// §F.3.3: P, Q, T, U and the lowercase p/q all denote properties
// (unclocked, clocked, top-level of either clock, or unrestricted). Every
// property-denoting category is recognized as a property.
TEST(NotationConventions, PropertyLettersAreProperties) {
  EXPECT_TRUE(DenotesProperty(NotationCategory::kUnclockedProperty));
  EXPECT_TRUE(DenotesProperty(NotationCategory::kClockedProperty));
  EXPECT_TRUE(DenotesProperty(NotationCategory::kUnclockedTopLevelProperty));
  EXPECT_TRUE(DenotesProperty(NotationCategory::kClockedTopLevelProperty));
  EXPECT_TRUE(DenotesProperty(NotationCategory::kProperty));
  for (const char* sym : {"P", "Q", "T", "U", "p", "q"}) {
    auto category = ClassifyAnnexFNotation(sym);
    ASSERT_TRUE(category.has_value()) << "symbol: " << sym;
    EXPECT_TRUE(DenotesProperty(*category)) << "symbol: " << sym;
  }
}

// §F.3.3 keeps the sequence and property families disjoint: a sequence
// category is not a property and a property category is not a sequence.
TEST(NotationConventions, SequenceAndPropertyFamiliesAreDisjoint) {
  EXPECT_FALSE(DenotesProperty(NotationCategory::kUnclockedSequence));
  EXPECT_FALSE(DenotesProperty(NotationCategory::kClockedSequence));
  EXPECT_FALSE(DenotesProperty(NotationCategory::kSequence));
  EXPECT_FALSE(DenotesSequence(NotationCategory::kUnclockedProperty));
  EXPECT_FALSE(DenotesSequence(NotationCategory::kClockedProperty));
  EXPECT_FALSE(DenotesSequence(NotationCategory::kUnclockedTopLevelProperty));
  EXPECT_FALSE(DenotesSequence(NotationCategory::kClockedTopLevelProperty));
  EXPECT_FALSE(DenotesSequence(NotationCategory::kProperty));
}

// §F.3.3: the terminal categories (Boolean expression, type, local/free
// checker variable, expression, assertion, integer constant) denote
// neither a sequence nor a property.
TEST(NotationConventions, TerminalCategoriesAreNeitherSequenceNorProperty) {
  for (NotationCategory category : {
           NotationCategory::kBooleanExpression,
           NotationCategory::kType,
           NotationCategory::kLocalVariableName,
           NotationCategory::kFreeCheckerVariableName,
           NotationCategory::kExpression,
           NotationCategory::kAssertion,
           NotationCategory::kNonNegativeIntegerConstant,
       }) {
    EXPECT_FALSE(DenotesSequence(category));
    EXPECT_FALSE(DenotesProperty(category));
  }
}

// §F.3.3 edge cases around the subscript convention: a zero or multi-digit
// subscript still resolves to the base letter's category, while a token
// that is only digits, or a trailing underscore with no digits, is not a
// subscripted notation and carries no convention.
TEST(NotationConventions, SubscriptEdgeCases) {
  EXPECT_EQ(ClassifyAnnexFNotation("R0"), NotationCategory::kUnclockedSequence);
  EXPECT_EQ(ClassifyAnnexFNotation("p_2"), NotationCategory::kProperty);
  EXPECT_FALSE(ClassifyAnnexFNotation("1").has_value());
  EXPECT_FALSE(ClassifyAnnexFNotation("123").has_value());
  EXPECT_FALSE(ClassifyAnnexFNotation("b_").has_value());
  EXPECT_FALSE(ClassifyAnnexFNotation("_1").has_value());
}

}  // namespace
