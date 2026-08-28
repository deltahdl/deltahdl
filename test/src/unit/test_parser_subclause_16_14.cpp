// §16.14 concurrent assertions that deltahdl does not evaluate, and the report
// that says so. The clause rules that "A property on its own is never
// evaluated for checking an expression. It shall be used within an assertion
// statement (see 16.2) for this to occur." A source that writes one of the
// five concurrent assertion statements of Syntax 16-18 has written that
// assertion statement, so every case here hands deltahdl a form it cannot
// evaluate and reads back the warning naming the reason, plus one control that
// hands it the form it can evaluate and reads back no warning at all.
//
// The cases go with the warning: as each form gains an evaluation path under
// #2923, #2924 and #2927, the case asserting it is unevaluated is replaced by
// one asserting what it evaluates to.
//
// The subclause here is §16.14 rather than §16.14.1 through §16.14.4 because
// the sentence quoted above is the parent clause's, and because one report
// covers all four statements.

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// How many §16.14 non-evaluation reports a run made. The control below rests
// on this rather than on the size of the whole record, so a report about some
// other rule can neither satisfy it nor break it.
int UnevaluatedReports(const ParseResult& r) {
  int count = 0;
  for (const auto& diag : r.diags) {
    if (diag.severity == DiagSeverity::kWarning && diag.subclause == "16.14" &&
        diag.message.find("concurrent assertion is not evaluated") !=
            std::string::npos) {
      ++count;
    }
  }
  return count;
}

// §16.14 Syntax 16-18 lists assume_property_statement among the concurrent
// assertion statements, and Parser::ParsePropertyAssertLike takes the
// clocked-boolean path only for assert, so an assume is skipped whatever its
// property_spec holds. The spec here is the one form deltahdl does evaluate,
// which is what shows the directive rather than the body is the reason.
TEST(ConcurrentAssertionEvaluationReporting, AssumePropertyIsNotEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedWarning(
      r.diags, "assume property is parsed and then discarded", 2, "16.14"));
}

// §16.14 Syntax 16-18 lists cover_property_statement, which
// Parser::ParseCoverProperty skips outright.
TEST(ConcurrentAssertionEvaluationReporting, CoverPropertyIsNotEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedWarning(
      r.diags, "cover property is parsed and then discarded", 2, "16.14"));
}

// §16.14 Syntax 16-18 lists cover_sequence_statement separately from
// cover_property_statement, and the report names the statement the source
// wrote rather than folding the two together.
TEST(ConcurrentAssertionEvaluationReporting, CoverSequenceIsNotEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedWarning(
      r.diags, "cover sequence is parsed and then discarded", 2, "16.14"));
}

// §16.14 Syntax 16-18 lists restrict_property_statement, which
// Parser::ParseRestrictProperty skips outright.
TEST(ConcurrentAssertionEvaluationReporting, RestrictPropertyIsNotEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedWarning(
      r.diags, "restrict property is parsed and then discarded", 2, "16.14"));
}

// §16.12.6: |-> is the overlapped implication operator, so the property is
// temporal rather than the sampled boolean deltahdl evaluates. #2924 and #2927
// cover the operators.
TEST(ConcurrentAssertionEvaluationReporting,
     OverlappedImplicationIsNotEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedWarning(r.diags, "its property is temporal", 2, "16.14"));
}

// §16.12.6: |=> is the nonoverlapped implication operator. It reaches the same
// branch as |-> by its own route through Parser::BodyHasTemporalOperator, so it
// takes its own case.
TEST(ConcurrentAssertionEvaluationReporting,
     NonoverlappedImplicationIsNotEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |=> b);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedWarning(r.diags, "its property is temporal", 2, "16.14"));
}

// §16.7: ## is the cycle delay range, and it is the third route into the
// temporal branch.
TEST(ConcurrentAssertionEvaluationReporting, CycleDelayIsNotEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedWarning(r.diags, "its property is temporal", 2, "16.14"));
}

// §16.14.5 allows a concurrent assertion outside procedural code to take its
// clock from a default clocking block rather than from a leading clocking
// event. deltahdl infers no clock, so an assert property written without one
// has nothing to sample its boolean on and is skipped even though it is an
// assert and even though its body is boolean.
TEST(ConcurrentAssertionEvaluationReporting,
     AssertWithoutAClockIsNotEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedWarning(
      r.diags, "its property_spec has no leading clocking event", 2, "16.14"));
}

// A clocked assert whose property_spec is not exhausted by one boolean
// expression: §16.12 admits the property operator and, since ParseExpr stops
// before it, the boolean leaves the rest of the spec unread. The report names
// this rather than the missing clock, because the clock is present.
TEST(ConcurrentAssertionEvaluationReporting,
     ClockedNonBooleanPropertyIsNotEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a and b);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedWarning(
      r.diags, "holds more than the @(event) boolean_expression", 2, "16.14"));
}

// THE CONTROL. §16.14 has the property within an assertion statement evaluated,
// and this is the one form deltahdl does evaluate: an assert property whose
// spec is a leading clocking event and a boolean.
// Parser::TryParseSimpleConcurrentProperty lowers it to a clocked process, so
// nothing is discarded and there is nothing to report. Without this case a
// warning on every concurrent assertion would satisfy all nine cases above.
TEST(ConcurrentAssertionEvaluationReporting, ClockedBooleanAssertIsEvaluated) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_EQ(UnevaluatedReports(r), 0);
}

}  // namespace
