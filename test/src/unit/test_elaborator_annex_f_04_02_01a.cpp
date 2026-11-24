#include <gtest/gtest.h>

#include <optional>

#include "elaborator/checker_rewrite.h"
#include "elaborator/checker_rewrite_algorithm.h"
#include "elaborator/rewrite_algorithm.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(CheckerRewriteAlgorithm, MainLoopHasSingleStage) {
  EXPECT_EQ(FirstCheckerRewriteStage(), CheckerRewriteStage::kCheckerInstances);
  EXPECT_EQ(NextCheckerRewriteStage(CheckerRewriteStage::kCheckerInstances),
            CheckerRewriteStage::kCheckerInstances);
}

TEST(CheckerRewriteAlgorithm, ActualIsTheBoundOneElseTheDeclaredDefault) {
  EXPECT_EQ(CheckerActualArgumentFor(true, false),
            ActualArgumentSource::kBoundInInstance);
  EXPECT_EQ(CheckerActualArgumentFor(true, true),
            ActualArgumentSource::kBoundInInstance);
  EXPECT_EQ(CheckerActualArgumentFor(false, true),
            ActualArgumentSource::kDeclaredDefault);
  EXPECT_EQ(CheckerActualArgumentFor(false, false), std::nullopt);
}

TEST(CheckerRewriteAlgorithm, UnboundInputFormalTakesItsDeclaredDefault) {
  ModuleDecl decl;
  decl.decl_kind = ModuleDeclKind::kChecker;
  decl.name = "chk";
  PortDecl a;
  a.direction = Direction::kInput;
  PortDecl b;
  b.direction = Direction::kInput;
  PortDecl c;
  c.direction = Direction::kInput;
  Expr c_default{};
  c.default_value = &c_default;
  PortDecl out;
  out.direction = Direction::kOutput;
  decl.ports = {a, b, c, out};
  CheckerRegistry reg;
  reg.Register(&decl);

  EXPECT_TRUE(reg.Flatten("chk", 2).legal);
  EXPECT_FALSE(reg.Flatten("chk", 1).legal);
  EXPECT_TRUE(reg.Flatten("chk", 3).legal);
  EXPECT_FALSE(reg.Flatten("chk", 4).legal);
}

TEST(CheckerRewriteAlgorithm, RewritesTheThreeFormalInputKinds) {
  EXPECT_TRUE(CheckerAlgorithmHandlesFormal(FormalKind::kUntyped));
  EXPECT_TRUE(CheckerAlgorithmHandlesFormal(FormalKind::kTypedNonMatching));
  EXPECT_TRUE(CheckerAlgorithmHandlesFormal(FormalKind::kTypedMatching));
}

TEST(CheckerRewriteAlgorithm, HasNoLocalVariableFormalStep) {
  EXPECT_FALSE(CheckerAlgorithmHandlesFormal(FormalKind::kLocalVariable));
}

TEST(CheckerRewriteAlgorithm, UntypedFormalSubstitution) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kUntyped,
                                          ActualNature::kDollarOrLvalue),
            ReferenceReplacement::kActualDirect);
  EXPECT_EQ(
      ReplaceCheckerFormalReference(FormalKind::kUntyped, ActualNature::kOther),
      ReferenceReplacement::kItemCastInferredType);
}

TEST(CheckerRewriteAlgorithm, TypedNonMatchingFormalCasts) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedNonMatching,
                                          ActualNature::kCastingType),
            ReferenceReplacement::kItemCastToFormalType);
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedNonMatching,
                                          ActualNature::kOther),
            ReferenceReplacement::kItemCastTypeOfFormal);
}

TEST(CheckerRewriteAlgorithm, TypedMatchingFormalSubstitution) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedMatching,
                                          ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kItemActual);
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedMatching,
                                          ActualNature::kOther),
            ReferenceReplacement::kParenthesizedActual);
}

TEST(CheckerRewriteAlgorithm,
     CastReplacedFormalIsNoVariableLvalueAnywhereInTheChecker) {
  CastReplacedFormalLvalueRule rule = CheckerCastReplacedFormalLvalueRule();
  EXPECT_FALSE(rule.replacement_may_be_lvalue);
  EXPECT_EQ(rule.scope, LvalueProhibitionScope::kWholeChecker);
}

TEST(CheckerRewriteAlgorithm, UntypedFormalIgnoresOtherStepsActualForms) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kUntyped,
                                          ActualNature::kCastingType),
            ReferenceReplacement::kItemCastInferredType);
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kUntyped,
                                          ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kItemCastInferredType);
}

TEST(CheckerRewriteAlgorithm, TypedNonMatchingIgnoresMethodOperandForm) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedNonMatching,
                                          ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kItemCastTypeOfFormal);
}

TEST(CheckerRewriteAlgorithm, TypedNonMatchingIgnoresDollarOrLvalueForm) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedNonMatching,
                                          ActualNature::kDollarOrLvalue),
            ReferenceReplacement::kItemCastTypeOfFormal);
}

TEST(CheckerRewriteAlgorithm, TypedMatchingParenthesizesUnlessMethodOperand) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedMatching,
                                          ActualNature::kCastingType),
            ReferenceReplacement::kParenthesizedActual);
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedMatching,
                                          ActualNature::kDollarOrLvalue),
            ReferenceReplacement::kParenthesizedActual);
}

TEST(CheckerRewriteAlgorithm, ParenthesesOmittedOnlyWhereTheReferenceHasThem) {
  EXPECT_FALSE(CheckerParenthesizedActualNeedsParentheses(true));
  EXPECT_TRUE(CheckerParenthesizedActualNeedsParentheses(false));
}

TEST(CheckerRewriteAlgorithm, FlattenedCheckerIsTheBareBody) {
  auto shape = FlattenedCheckerForm();
  EXPECT_FALSE(shape.prepends_local_var_declarations);
  EXPECT_FALSE(shape.appends_match_item_assignments);
  EXPECT_FALSE(shape.enclosed_in_parentheses);
  EXPECT_TRUE(FlattenedForm(FlattenTarget::kProperty).enclosed_in_parentheses);
}

}  // namespace
