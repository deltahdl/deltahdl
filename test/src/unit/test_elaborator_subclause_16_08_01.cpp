#include <gtest/gtest.h>

#include <string>

#include "elaborator/rtlir.h"
#include "elaborator/typed_sequence_formal.h"
#include "fixture_elaborator.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(TypedSequenceFormal, AllowedTypeKindsIncludeUntypedSequenceEventIntegral) {
  // §16.8.1: a formal argument's type may be `untyped`, `sequence`, `event`,
  // or one of the types allowed in §16.6.
  EXPECT_TRUE(IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kUntyped));
  EXPECT_TRUE(IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kSequence));
  EXPECT_TRUE(IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kEvent));
  EXPECT_TRUE(
      IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kIntegralOrUserType));
}

TEST(TypedSequenceFormal, ForbiddenTypeKindRejected) {
  // §16.8.1: anything outside the allowed list is not a valid sequence
  // formal type.
  EXPECT_FALSE(IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kForbidden));
}

TEST(TypedSequenceFormal, SequenceTypedRefLegalPlaces) {
  // §16.8.1(a): a reference to a `sequence`-typed formal shall stand in a
  // sequence_expr place, or as the operand of `triggered`/`matched`.
  EXPECT_TRUE(IsSequenceTypedFormalRefLegal(
      SequenceTypedFormalRefPlace::kSequenceExprPosition));
  EXPECT_TRUE(IsSequenceTypedFormalRefLegal(
      SequenceTypedFormalRefPlace::kTriggeredMethodOperand));
  EXPECT_TRUE(IsSequenceTypedFormalRefLegal(
      SequenceTypedFormalRefPlace::kMatchedMethodOperand));
  EXPECT_FALSE(IsSequenceTypedFormalRefLegal(
      SequenceTypedFormalRefPlace::kOtherPosition));
}

TEST(TypedSequenceFormal, EventTypedRefRequiresEventExpressionPosition) {
  // §16.8.1(b): a reference to an `event`-typed formal shall be in a place
  // where an event_expression may be written.
  EXPECT_TRUE(
      IsEventTypedFormalRefLegal(/*in_event_expression_position=*/true));
  EXPECT_FALSE(
      IsEventTypedFormalRefLegal(/*in_event_expression_position=*/false));
}

TEST(TypedSequenceFormal, SequenceTypedFormalForbiddenAsGotoOperand) {
  // §16.8.1 (cross-link to §16.9.2): a sequence-typed formal may not be the
  // expression_or_dist operand of a goto_repetition.
  EXPECT_FALSE(IsSequenceTypedFormalAllowedAsGotoOperand());
}

TEST(TypedSequenceFormal, TypedFormalLvalueInMatchItemOnlyForLocalVar) {
  // §16.8.1 (cross-link to §16.11/§16.10): a typed formal reference inside
  // a sequence_match_item shall not stand as the variable_lvalue in an
  // operator_assignment or inc_or_dec_expression — unless the formal is a
  // local variable formal.
  EXPECT_FALSE(IsTypedFormalAllowedAsMatchItemLvalue(
      /*is_local_var_formal=*/false));
  EXPECT_TRUE(IsTypedFormalAllowedAsMatchItemLvalue(
      /*is_local_var_formal=*/true));
}

TEST(TypedSequenceFormal, DelayAndRepetitionIndexTypeRestricted) {
  // §16.8.1: a typed formal referenced inside a cycle_delay_range, a
  // boolean_abbrev, or a sequence_abbrev (terms from §16.9.2) shall be of
  // type shortint, int, or longint.
  EXPECT_TRUE(IsDelayOrRepetitionIndexTypeAllowed(
      SequenceFormalIntegralType::kShortint));
  EXPECT_TRUE(
      IsDelayOrRepetitionIndexTypeAllowed(SequenceFormalIntegralType::kInt));
  EXPECT_TRUE(IsDelayOrRepetitionIndexTypeAllowed(
      SequenceFormalIntegralType::kLongint));
  EXPECT_FALSE(IsDelayOrRepetitionIndexTypeAllowed(
      SequenceFormalIntegralType::kOtherIntegral));
}

TEST(TypedSequenceFormal, SubstitutionModePicksLvalueVsCast) {
  // §16.8.1(c): if the actual is a variable_lvalue, mutate-and-assign-back
  // semantics apply. Otherwise the actual is cast to the formal's type
  // before substitution in the §F.4.1 rewriting algorithm.
  EXPECT_EQ(TypedFormalSubstitution(/*actual_is_variable_lvalue=*/true),
            TypedFormalSubstitutionMode::kAssignBackAfterUpdate);
  EXPECT_EQ(TypedFormalSubstitution(/*actual_is_variable_lvalue=*/false),
            TypedFormalSubstitutionMode::kCastBeforeSubstitution);
}

TEST(TypedSequenceFormal, UntypedKeywordRequiredAfterTypedFormal) {
  // §16.8.1: an untyped formal that follows a typed formal in the list must
  // spell `untyped` explicitly, since a bare name would otherwise inherit
  // the preceding data type.
  EXPECT_TRUE(IsUntypedKeywordRequired(/*prev_formal_in_list_was_typed=*/true,
                                       /*this_formal_intended_untyped=*/true));
  EXPECT_FALSE(IsUntypedKeywordRequired(
      /*prev_formal_in_list_was_typed=*/false,
      /*this_formal_intended_untyped=*/true));
  EXPECT_FALSE(IsUntypedKeywordRequired(
      /*prev_formal_in_list_was_typed=*/true,
      /*this_formal_intended_untyped=*/false));
}

TEST(TypedSequenceFormal, EventTypedFormalRejectsEdgeIdentifierActual) {
  // §16.8.1: a formal typed `event` may not receive an actual that will be
  // combined with an edge_identifier to build an event_expression.
  EXPECT_FALSE(IsEventTypedFormalCompatibleWithEdgeIdentifierUse(
      /*formal_typed_event=*/true,
      /*actual_combined_with_edge_identifier=*/true));
  EXPECT_TRUE(IsEventTypedFormalCompatibleWithEdgeIdentifierUse(
      /*formal_typed_event=*/true,
      /*actual_combined_with_edge_identifier=*/false));
  EXPECT_TRUE(IsEventTypedFormalCompatibleWithEdgeIdentifierUse(
      /*formal_typed_event=*/false,
      /*actual_combined_with_edge_identifier=*/true));
}

// The process a static concurrent assertion is lowered to, an always_ff under
// §16.14.5, or nullptr where the module holds none.
const RtlirProcess* AssertionProcess(const RtlirModule* mod) {
  for (const auto& p : mod->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysFF) return &p;
  }
  return nullptr;
}

// The clocking event of the one assertion in `src`, checked to be the single
// event posedge clk.
void ExpectClockedOnPosedgeClk(const std::string& src) {
  ElabFixture f;
  auto* design = ElaborateSrc(src, f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  const RtlirProcess* p = AssertionProcess(design->top_modules[0]);
  ASSERT_NE(p, nullptr);
  ASSERT_EQ(p->sensitivity.size(), 1u);
  EXPECT_EQ(p->sensitivity[0].edge, Edge::kPosedge);
  ASSERT_NE(p->sensitivity[0].signal, nullptr);
  EXPECT_EQ(p->sensitivity[0].signal->text, "clk");
}

// §16.8.1 (b) with §16.16 (f): an assertion whose property_spec is an instance
// of a sequence clocked by an event formal is clocked by the formal's actual,
// so s_ev(posedge clk, a) is clocked on posedge clk and not on the formal ev.
TEST(TypedSequenceFormal, AnInstancesClockTakesTheEventFormalsActual) {
  ExpectClockedOnPosedgeClk(
      "module t;\n"
      "  logic clk, a;\n"
      "  sequence s_ev(event ev, untyped x); @(ev) x ##2 !x; endsequence\n"
      "  cover property (s_ev(posedge clk, a));\n"
      "endmodule\n");
}

// §16.8 and §16.8.1 (c) with §16.16 (f): a data-typed formal under an edge in
// the clock stands for its actual, so s_ev2(clk, a) with `@(posedge sig)` is
// clocked on posedge clk.
TEST(TypedSequenceFormal, AnInstancesClockTakesTheSignalFormalsActual) {
  ExpectClockedOnPosedgeClk(
      "module t;\n"
      "  logic clk, a;\n"
      "  sequence s_ev2(reg sig, x); @(posedge sig) x ##2 !x; endsequence\n"
      "  cover property (s_ev2(clk, a));\n"
      "endmodule\n");
}

}  // namespace
