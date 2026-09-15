// §16.2 names the four kinds of assertion statement and the two kinds of
// assertion, and rules on how they combine: an assertion statement is an
// assert, an assume, a cover or a restrict, and there is no immediate restrict
// assertion statement. The restrict form exists for formal verification, and
// the clause has a simulator not check its property. Each case here hands the
// parser one of those rules and reads back what it reports, so a restrict
// written where §16.2 has none is refused under this clause, and a restrict
// property left unchecked draws no report, since leaving it unchecked is what
// the clause specifies rather than a shortfall of the tool.

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §16.2: there is no immediate restrict assertion statement. A restrict
// written as a procedural statement is refused where it stands, under this
// clause, since the rule that rules it out is this clause's.
TEST(AssertionKindsParsing, ImmediateRestrictIsRefused) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  initial restrict (a);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "restrict has no immediate", 3, "16.2"));
}

// §16.2: a restrict specifies its property as a constraint on formal
// verification computations, and simulators do not check the property. So a
// restrict property whose spec the clocked boolean path could have evaluated
// is accepted and draws no non-evaluation report: the report names what this
// tool cannot evaluate, and this is what the standard has it not evaluate.
TEST(AssertionKindsParsing, RestrictPropertyIsAcceptedWithoutAReport) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, ctr;\n"
      "  restrict property (@(posedge clk) ctr == '0);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(ReportedWarning(r.diags, "concurrent assertion is not evaluated",
                               3, "16.14"));
}

// §16.2 lists assert, assume and cover as the other three kinds, each with an
// immediate form that follows simulation event semantics as a statement in a
// procedural block does. All three are accepted where a statement is, with no
// error, which is the control the refusal above needs: it is of the fourth
// kind alone, not of the procedural position.
TEST(AssertionKindsParsing, ImmediateAssertAssumeAndCoverAreAccepted) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    assert (a);\n"
      "    assume (a);\n"
      "    cover (a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
