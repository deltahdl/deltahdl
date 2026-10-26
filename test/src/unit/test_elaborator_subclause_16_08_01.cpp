#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/property_instance.h"
#include "elaborator/rtlir.h"
#include "elaborator/typed_sequence_formal.h"
#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
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

// One clocking event written as its edge keyword and its signal's name.
std::string EventText(const EventExpr& ev) {
  std::string edge;
  if (ev.edge == Edge::kPosedge) edge = "posedge ";
  if (ev.edge == Edge::kNegedge) edge = "negedge ";
  return edge + std::string(ev.signal != nullptr ? ev.signal->text : "");
}

// The clocking events the process of the static concurrent assertion in `src`
// wakes on, an always_ff under §16.14.5, each as EventText writes it; empty
// where the source does not elaborate cleanly.
std::vector<std::string> AssertionWakeEvents(const std::string& src) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(src, f, "t");
  std::vector<std::string> events;
  if (design == nullptr || f.has_errors || design->top_modules.empty()) {
    return events;
  }
  for (const RtlirProcess& p : design->top_modules[0]->processes) {
    if (p.kind != RtlirProcessKind::kAlwaysFF) continue;
    for (const EventExpr& ev : p.sensitivity) events.push_back(EventText(ev));
  }
  return events;
}

// §16.8.1 (b) with §16.16 (f): an assertion whose property_spec is an instance
// of a sequence clocked by an event formal is clocked by the formal's actual,
// so s_ev(posedge clk, a) is clocked on posedge clk and not on the formal ev.
TEST(TypedSequenceFormal, AnInstancesClockTakesTheEventFormalsActual) {
  EXPECT_EQ(
      AssertionWakeEvents(
          "module t;\n"
          "  logic clk, a;\n"
          "  sequence s_ev(event ev, untyped x); @(ev) x ##2 !x; endsequence\n"
          "  cover property (s_ev(posedge clk, a));\n"
          "endmodule\n"),
      std::vector<std::string>{"posedge clk"});
}

// §16.8 and §16.8.1 (c) with §16.16 (f): a data-typed formal under an edge in
// the clock stands for its actual, so s_ev2(clk, a) with `@(posedge sig)` is
// clocked on posedge clk.
TEST(TypedSequenceFormal, AnInstancesClockTakesTheSignalFormalsActual) {
  EXPECT_EQ(
      AssertionWakeEvents(
          "module t;\n"
          "  logic clk, a;\n"
          "  sequence s_ev2(reg sig, x); @(posedge sig) x ##2 !x; endsequence\n"
          "  cover property (s_ev2(clk, a));\n"
          "endmodule\n"),
      std::vector<std::string>{"posedge clk"});
}

// §16.8.1 (a) with §16.12.18: an instance of a property whose body is the
// clocked boolean form takes the boolean substitution unless an actual is one
// the boolean does not read. A list of names bound to the formal the boolean
// is, `(a, note)`, stands there as the sequence it reads as, so that instance
// is evaluated as the body's tree. The list bound to a formal the boolean is
// not, an expression or no actual at all bound to the boolean's formal, a
// boolean that is no formal, and one that is more than a formal leave the
// substitution in place; a body of another form is always the tree.
TEST(TypedSequenceFormal, AListBoundToTheBooleanFormalTakesTheTree) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  function void note; endfunction\n"
      "  property p(q, r); @(posedge clk) q; endproperty\n"
      "  property w(q); @(posedge clk) a; endproperty\n"
      "  property v(q); @(posedge clk) q && b; endproperty\n"
      "  property t(q); @(posedge clk) q |-> b; endproperty\n"
      "  assert property (p((a, note), c));\n"
      "  assert property (p(c, (a, note)));\n"
      "  assert property (p(b, c));\n"
      "  assert property (p(, c));\n"
      "  assert property (w((a, note)));\n"
      "  assert property (v((a, note)));\n"
      "  assert property (t(b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  std::vector<const ModuleItem*> decls;
  std::vector<const Expr*> instances;
  for (const ModuleItem* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) decls.push_back(item);
    if (item->kind == ModuleItemKind::kAssertProperty) {
      instances.push_back(item->assert_expr);
    }
  }
  ASSERT_EQ(decls.size(), 4u);
  ASSERT_EQ(instances.size(), 7u);
  const std::vector<const ModuleItem*> kDeclOf = {
      decls[0], decls[0], decls[0], decls[0], decls[1], decls[2], decls[3]};
  const std::vector<bool> kSubstituted = {false, true, true, true,
                                          true,  true, false};
  for (size_t i = 0; i < instances.size(); ++i) {
    ASSERT_NE(instances[i], nullptr) << "instance " << i;
    EXPECT_EQ(TakesBooleanSubstitution(instances[i], kDeclOf[i]),
              kSubstituted[i])
        << "instance " << i;
  }
}

// How many §16.8.1 errors the run reported on `line` whose message holds
// `message`, which is one for each breach the cases below name.
std::ptrdiff_t ReportsOnLine(const std::vector<Diagnostic>& diags,
                             uint32_t line, std::string_view message) {
  return std::ranges::count_if(diags, [&](const Diagnostic& d) {
    return d.severity == DiagSeverity::kError && d.loc.line == line &&
           d.subclause == "16.8.1" &&
           d.message.find(message) != std::string::npos;
  });
}

// §16.8.1: a typed formal argument stands as the variable_lvalue of a match
// item's assignment or increment only where it is a local variable formal
// argument. x of s1 and y of s2 are typed and not local, so both are
// reported; z of s3 is local and w of s4 untyped, and neither is. p shows a
// property's sequences held to the same rule.
TEST(TypedSequenceFormal, ATypedFormalAssignedInAMatchItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  sequence s1(int x);\n"
      "    (a, x = 1) ##1 b;\n"
      "  endsequence\n"
      "  sequence s2(bit [3:0] y);\n"
      "    (a, y++) ##1 b;\n"
      "  endsequence\n"
      "  sequence s3(local inout int z);\n"
      "    (a, z += 1);\n"
      "  endsequence\n"
      "  sequence s4(w);\n"
      "    (a, w = 1);\n"
      "  endsequence\n"
      "  property p(int x);\n"
      "    @(posedge clk) (a, x = 1) |-> b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the typed formal argument 'x' of 's1' is "
                            "assigned in a sequence match item",
                            4, "16.8.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the typed formal argument 'y' of 's2' is "
                            "assigned in a sequence match item",
                            7, "16.8.1"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "'z' of 's3'", 10, "16.8.1"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "'w' of 's4'", 13, "16.8.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the typed formal argument 'x' of 'p' is "
                            "assigned in a sequence match item",
                            16, "16.8.1"));
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 4, "'x' of 's1'"), 1);
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 7, "'y' of 's2'"), 1);
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 16, "'x' of 'p'"), 1);
}

// §16.8.1: a typed formal argument referenced in a cycle delay range or a
// repetition's bound is of type shortint, int or longint. d of s1, n of s2
// and g of s3 are not, so each is reported; the three of s4 are, and d of
// s5 is untyped, so neither line is. v of s6 is of another type but bounds
// nothing, the int k bounding its one delay, so its line is not either. A
// bound written alone, `##d` or `[*n]`, is the least and the greatest count
// at once, and is one breach.
TEST(TypedSequenceFormal, ABoundOfAnotherTypeIsReported) {
  const char* const kReport =
      "bounds a cycle delay or a repetition but is of a type other than "
      "shortint, int or longint";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  sequence s1(bit [3:0] d);\n"
      "    a ##d b;\n"
      "  endsequence\n"
      "  sequence s2(byte n);\n"
      "    a ##1 b[*n];\n"
      "  endsequence\n"
      "  sequence s3(logic [7:0] g);\n"
      "    a ##1 b[->g];\n"
      "  endsequence\n"
      "  sequence s4(shortint d1, int d2, longint d3);\n"
      "    a ##d1 b ##[d2:d3] a[=d1];\n"
      "  endsequence\n"
      "  sequence s5(d);\n"
      "    a ##d b;\n"
      "  endsequence\n"
      "  sequence s6(bit [3:0] v, int k);\n"
      "    v[0] ##k b;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      std::string("the formal argument 'd' of 's1' ") + kReport, 4, "16.8.1"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      std::string("the formal argument 'n' of 's2' ") + kReport, 7, "16.8.1"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      std::string("the formal argument 'g' of 's3' ") + kReport, 10, "16.8.1"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 13, "16.8.1"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 16, "16.8.1"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 19, "16.8.1"));
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 4, "'d' of 's1'"), 1);
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 7, "'n' of 's2'"), 1);
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 10, "'g' of 's3'"), 1);
}

// §16.8.1: a formal argument of type sequence is not the operand of a goto
// repetition. q of s1 is; s2 repeats b, and q of s3 is untyped.
TEST(TypedSequenceFormal, ASequenceFormalAsAGotoOperandIsReported) {
  const char* const kReport =
      "is of type sequence and is the operand of a "
      "goto repetition";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  sequence s1(sequence q);\n"
      "    q[->1] ##1 b;\n"
      "  endsequence\n"
      "  sequence s2(sequence q);\n"
      "    q ##1 b[->1];\n"
      "  endsequence\n"
      "  sequence s3(q);\n"
      "    q[->1] ##1 b;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      std::string("the formal argument 'q' of 's1' ") + kReport, 4, "16.8.1"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 7, "16.8.1"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 10, "16.8.1"));
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 4, "'q' of 's1'"), 1);
}

// §16.8.1: the three rules hold inside a group that `or` makes a sequence of
// its own, standing as one operand of the chain around it: d of s1 bounds a
// delay of one alternative, x of s2 is assigned in a match item of one, and
// q of s3 is repeated by goto in one.
TEST(TypedSequenceFormal, AFormalInsideANestedGroupIsHeldToTheRules) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  sequence s1(bit [3:0] d);\n"
      "    a ##1 (a ##d b or b) ##1 b;\n"
      "  endsequence\n"
      "  sequence s2(int x);\n"
      "    a ##1 ((a, x = 1) or b);\n"
      "  endsequence\n"
      "  sequence s3(sequence q);\n"
      "    a ##1 (b or q[->1]);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the formal argument 'd' of 's1' bounds a cycle "
                            "delay or a repetition",
                            4, "16.8.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the typed formal argument 'x' of 's2' is "
                            "assigned in a sequence match item",
                            7, "16.8.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the formal argument 'q' of 's3' is of type "
                            "sequence and is the operand of a goto repetition",
                            10, "16.8.1"));
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 4, "'d' of 's1'"), 1);
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 7, "'x' of 's2'"), 1);
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), 10, "'q' of 's3'"), 1);
}

}  // namespace
