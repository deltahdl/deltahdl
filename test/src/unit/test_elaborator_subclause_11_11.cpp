// §11.11 gives a min:typ:max expression three values and says "the three
// values allow a design to be tested with minimum, typical, or maximum delay
// values", so which of the three a constant expression folds to is one setting
// for a whole elaboration. DelayModeGuard in src/elaborator/const_eval.h
// installs that setting and ActiveDelayMode answers it; these cases are over
// what ConstEvalFull in src/elaborator/const_eval_func.cpp does with it.
//
// The design each case elaborates writes the triple in parentheses, which
// A.8.4 admits as `constant_primary ::= ( constant_mintypmax_expression )` and
// Parser::ParseParenExpr in src/parser/expr_parser_aux.cpp builds into an
// ExprKind::kMinTypMax with the three members in Expr::lhs, Expr::condition and
// Expr::rhs.
//
// The triple is 11:22:33 so that no member coincides with another, with its
// position among the three, or with the 0 a fold that gave up leaves in
// RtlirParamDecl::resolved_value. A triple of 0:1:2 would let a folder that
// returned the position it selected, or one that folded nothing at all, answer
// a case that asked for the minimum.

#include <cstdint>
#include <string>
#include <string_view>

#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

// Elaborates the one design these cases share and answers what its parameter
// folded to, so that each case states only which mode was installed and which
// member came back.
int64_t FoldedTripleParam(ElabFixture& f) {
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = (11:22:33);\n"
      "endmodule\n",
      f);
  if (design == nullptr) {
    ADD_FAILURE() << "the source did not elaborate, so nothing folded";
    return 0;
  }
  EXPECT_FALSE(f.has_errors);
  const auto* p = FindParam(design, "m", "P");
  if (p == nullptr) {
    ADD_FAILURE() << "the elaborated design declares no parameter P";
    return 0;
  }
  return p->resolved_value;
}

// §11.11 orders the three "minimum, typical, and maximum values -- in that
// order", and the typical member is what the folder takes when nothing has
// asked for another. This is what a run given no --mintypmax gets.
TEST(MinTypMaxElaboration, TypicalMemberFoldsWhenNoDelayModeGuardIsLive) {
  ElabFixture f;
  EXPECT_EQ(FoldedTripleParam(f), 22);
}

// The minimum member, which §11.11's "tested with minimum ... delay values" is
// about. Nothing but the live guard differs from the case above.
TEST(MinTypMaxElaboration, MinimumMemberFoldsWhileAMinimumGuardIsLive) {
  ElabFixture f;
  DelayModeGuard guard(DelayMode::kMin);
  EXPECT_EQ(FoldedTripleParam(f), 11);
}

// The maximum member, the third of the three §11.11 names.
TEST(MinTypMaxElaboration, MaximumMemberFoldsWhileAMaximumGuardIsLive) {
  ElabFixture f;
  DelayModeGuard guard(DelayMode::kMax);
  EXPECT_EQ(FoldedTripleParam(f), 33);
}

// The guard restores the mode it found rather than writing the default back, so
// one elaboration cannot leak its mode into the next.
//
// The outer guard names the maximum on purpose. A destructor that assigned
// DelayMode::kTyp instead of the mode it saved would satisfy a case whose outer
// mode was already the typical one, because the two answers coincide there.
// Here such a destructor folds 22 where 33 is required.
TEST(MinTypMaxElaboration, AGuardRestoresTheModeItFoundRatherThanTheDefault) {
  DelayModeGuard outer(DelayMode::kMax);
  {
    ElabFixture under_inner;
    DelayModeGuard inner(DelayMode::kMin);
    EXPECT_EQ(FoldedTripleParam(under_inner), 11);
  }
  EXPECT_EQ(ActiveDelayMode(), DelayMode::kMax);
  ElabFixture after_inner;
  EXPECT_EQ(FoldedTripleParam(after_inner), 33);
}

// §11.11 says the form is an expression and not a delay alone -- "Values
// expressed in min:typ:max format can be used in expressions. The min:typ:max
// format can be used wherever expressions can appear" -- so it stands as an
// operand, and an operand is sized. InferExprWidth answered 0 for it, which
// sizes it as nothing wherever a context reads a width: a concatenation holding
// one contributes no bits for it and is wrong about how many it moved.
//
// Which member's width it takes is what Example 1 settles. `(a:b:c) + (d:e:f)`
// is read member by member -- "The minimum value is the sum of a+d; the typical
// value is b+e; the maximum value is c+f" -- so the form stands for the one
// member the run selects, and its width is that member's rather than anything
// composed of the three. The members below are sized 4, 8 and 16 bits, all
// different from each other and from the 0 the case is against, so no
// coincidence answers for the rule.
constexpr std::string_view kSizedTriple = "(4'd1:8'd2:16'd3)";

TEST(MinTypMaxElaboration, WidthIsTheTypicalMembersByDefault) {
  EvalFixture f;
  auto* e = ParseExprFrom(std::string(kSizedTriple), f);
  ASSERT_NE(e, nullptr);
  ASSERT_EQ(e->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(InferExprWidth(e, {}), 8u);
}

// The minimum member under the mode that selects it, so the width follows the
// same member the fold does rather than one the code happened to pick. Without
// this a width that always answered the typical member would satisfy the case
// above.
TEST(MinTypMaxElaboration, WidthFollowsTheSelectedMember) {
  EvalFixture f;
  auto* e = ParseExprFrom(std::string(kSizedTriple), f);
  ASSERT_NE(e, nullptr);
  DelayModeGuard guard(DelayMode::kMin);
  EXPECT_EQ(InferExprWidth(e, {}), 4u);
}

// And the maximum, whose member is a third width again: the three differ, which
// §11.11 permits by requiring no relation between them, so a rule that took the
// widest or the narrowest is told from one that takes the selected member.
TEST(MinTypMaxElaboration, WidthTakesNeitherTheWidestNorTheNarrowest) {
  EvalFixture f;
  auto* e = ParseExprFrom(std::string(kSizedTriple), f);
  ASSERT_NE(e, nullptr);
  DelayModeGuard guard(DelayMode::kMax);
  EXPECT_EQ(InferExprWidth(e, {}), 16u);
}

}  // namespace
