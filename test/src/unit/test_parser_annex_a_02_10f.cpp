// §A.2.10's property_spec, property_expr and sequence_expr, held to the spec
// of a concurrent assertion statement wherever the evaluation's own parse,
// Parser::TryParseSimpleConcurrentProperty, gives it up: a spec the grammar
// admits is reported as one this tool does not evaluate (§16.14), and one it
// does not admit is an error, reported at the furthest point no reading of it
// gets past.
//
// Each malformed spec below writes the point the report stands at on a line
// of its own, so a reading that broke off sooner or got further reports on
// another line. A spec that writes a construct well and then breaks puts the
// break on the line after the construct; one that breaks inside a construct
// breaks once more on a later line, so the evaluation's parse rejects it
// whatever it makes of the construct.

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kNotAdmitted = "is not one the grammar admits";

// A spec and the line its report stands on, the spec's first line being
// line 2.
struct Malformed {
  const char* spec;
  uint32_t line;
};

// `statement` with `spec` in its parentheses, on line 2 of a module.
ParseResult ParseSpec(const std::string& statement, const std::string& spec) {
  return Parse("module m;\n  " + statement + " (" + spec + ");\nendmodule\n");
}

void ExpectNotAdmitted(const std::string& statement,
                       const std::vector<Malformed>& cases) {
  for (const Malformed& c : cases) {
    SCOPED_TRACE(c.spec);
    auto r = ParseSpec(statement, c.spec);
    EXPECT_TRUE(ReportedError(r.diags, kNotAdmitted, c.line, "A.2.10"));
  }
}

// The constructs of the grammar, each written well and followed by a
// break, so the report stands on the line after the construct.
TEST(PropertySpecGrammar, AWellWrittenConstructIsReadPast) {
  ExpectNotAdmitted(
      "assert property",
      {
          {"@(posedge clk) disable iff (rst) a ##1\nb dist zz", 3},
          {"@clk a ##1\nb dist zz", 3},
          {"a and b or c intersect d within e throughout f |-> g |=> h "
           "#-# i #=# j until k s_until l until_with m s_until_with n "
           "implies o iff p ##1\nq dist zz",
           3},
          {"##1 ##[1:2] ##[*] ##[+] ##[0:$] a ##1\nb dist zz", 3},
          {"a ##1 @(posedge clk) b ##1\nc dist zz", 3},
          {"not nexttime s_nexttime [2] always [1:$] s_eventually [1:3] "
           "s_always [1:2] eventually [1:2] accept_on (r) reject_on (r) "
           "sync_accept_on (r) sync_reject_on (r) a ##1\nb dist zz",
           3},
          {"strong(a ##1 b) and weak(c) ##1\nd dist zz", 3},
          {"first_match(a ##1 b, x = 1) ##1\nc dist zz", 3},
          {"if (a) b else c ##1\nd dist zz", 3},
          {"(if (a) b) ##1\nc dist zz", 3},
          {"(if (a) b else c) ##1\nd dist zz", 3},
          {"(case (s) 1, 2: a; default: b; endcase) ##1\nc dist zz", 3},
          {"(a, x = 1, y += 2, z++, ++w, --v, $display(\"m\"), f(q)) ##1\n"
           "b dist zz",
           3},
          {"pkg::s(a ##1 b) and top.u.s(a ##1 b) ##1\nc dist zz", 3},
          {"s(, a ##1 b, $, .p(c ##1 d), .q(), posedge clk iff en or "
           "negedge rst, ) ##1\nc dist zz",
           3},
          {"a[+] ##1 b[*] ##1 c[*2] ##1 d[->1:3] ##1 e[=2] ##1\nf dist zz", 3},
          {"s(a ##1 b)[*2] ##1\nc dist zz", 3},
      });
}

// A clocking event, a disable condition or a cycle delay broken where the
// line after the first starts.
TEST(PropertySpecGrammar, ABrokenClockConditionOrDelayIsReportedWhereItBreaks) {
  ExpectNotAdmitted("assert property",
                    {
                        {"@(posedge clk\n] a ##1\nb dist zz", 3},
                        {"@(posedge +\n) a ##1\nb dist zz", 3},
                        {"@\n7 a ##1\nb dist zz", 3},
                        {"disable\n(rst) a ##1\nb dist zz", 3},
                        {"disable iff\nrst a ##1\nb dist zz", 3},
                        {"disable iff (rst\nb) a ##1\nc dist zz", 3},
                        {"disable iff (\n) a ##1\nb dist zz", 3},
                        {"a ##[*\n1] b ##1\nc dist zz", 3},
                        {"a ##[1\n] b ##1\nc dist zz", 3},
                        {"a ##[1:\n] b ##1\nc dist zz", 3},
                        {"a ##[1:2\nb ##1\nc dist zz", 3},
                        {"a ##\n] b ##1\nc dist zz", 3},
                        {"a ##1 @(posedge clk\n] b ##1\nc dist zz", 3},
                        {"a ##1 @(posedge clk)\n] ##1\nc dist zz", 3},
                    });
}

// An operator written before its operand, broken in what it reads before
// the operand or in the operand.
TEST(PropertySpecGrammar, ABrokenPrefixOperatorIsReportedWhereItBreaks) {
  ExpectNotAdmitted("assert property",
                    {
                        {"nexttime [1\n:2] a ##1\nb dist zz", 3},
                        {"s_always [1:\n$] a ##1\nb dist zz", 3},
                        {"s_always\na ##1\nb dist zz", 3},
                        {"always [1:2]\n] ##1\nb dist zz", 3},
                        {"always [\n] a ##1\nb dist zz", 3},
                        {"eventually [1:2]\n] ##1\nb dist zz", 3},
                        {"accept_on\na ##1\nb dist zz", 3},
                        {"accept_on (r)\n] ##1\nb dist zz", 3},
                        {"strong\na ##1\nb dist zz", 3},
                        {"if\na ##1\nb dist zz", 3},
                        {"if (a)\n] ##1\nb dist zz", 3},
                        {"if (a) b else\n] ##1\nc dist zz", 3},
                        {"case\ns ##1\nb dist zz", 3},
                        {"case (s)\n] endcase ##1\nb dist zz", 3},
                        {"case (s) 1\n; endcase ##1\nb dist zz", 3},
                        {"case (s) 1:\n] endcase ##1\nb dist zz", 3},
                        {"case (s) 1: a;\n] endcase ##1\nb dist zz", 3},
                        {"(case (s) 1: a\n) ##1\nb dist zz", 3},
                    });
}

// An operand broken: a name or a group with nothing a chain reads after
// it, a group, an instance or its actual arguments, a repetition or a
// match item.
TEST(PropertySpecGrammar, ABrokenOperandIsReportedWhereItBreaks) {
  ExpectNotAdmitted("assert property",
                    {
                        {"(a)\n(b) ##1\nc dist zz", 3},
                        {"x\ny ##1\nb dist zz", 3},
                        {"a and\n] ##1\nb dist zz", 3},
                        {"(a ##1\n]) ##1\nb dist zz", 3},
                        {"(a ##1 b)[\n=2] ##1\nc dist zz", 3},
                        {"(a ##1 b)\n[3] ##1\nc dist zz", 3},
                        {"(a ##1 b\n; c) ##1\nd dist zz", 3},
                        {"strong(a\n, x = 1) ##1\nb dist zz", 3},
                        {"(a ##1 b,\nc) ##1\nd dist zz", 3},
                        {"(a ##1 b, -x\n) ##1\nd dist zz", 3},
                        {"(a ##1 b, x =\n]) ##1\nd dist zz", 3},
                        {"(a ##1 b,\n]) ##1\nd dist zz", 3},
                        {"a[+\n2] ##1\nb dist zz", 3},
                        {"(a[*2\n; b) ##1\nc dist zz", 3},
                        {"s(a ##1 b)[\n->2] ##1\nc dist zz", 3},
                        {"top.\n(a ##1 b) ##1\nc dist zz", 3},
                        {"s(a ##1\n]) ##1\nc dist zz", 3},
                        {"s(a ##1 b\n; c) ##1\nd dist zz", 3},
                        {"s(.\n(a)) ##1\nc dist zz", 3},
                        {"s(.p\na) ##1\nc dist zz", 3},
                        {"s(.p(\n])) ##1\nc dist zz", 3},
                        {"s(.p(a ##1 b\n; c)) ##1\nd dist zz", 3},
                        {"s(posedge\n]) ##1\nc dist zz", 3},
                        {"s(posedge clk iff\n]) ##1\nc dist zz", 3},
                        {"s(posedge clk or\n]) ##1\nc dist zz", 3},
                    });
}

// §16.14.3: a cover sequence statement's spec is a sequence_expr after its
// clock and its disable condition, so a property operator, binary or
// written before its operand, is no part of it; first_match and the
// sequence operators are.
TEST(PropertySpecGrammar, ACoverSequenceSpecAdmitsNoPropertyOperator) {
  ExpectNotAdmitted(
      "cover sequence",
      {
          {"@(posedge clk) first_match(a ##1 b) and c ##1\nd dist zz", 3},
          {"a\n|-> b ##1\nc dist zz", 3},
          {"a ##1\nnot b ##1\nc dist zz", 3},
      });
}

// The grammar is held to the spec of every concurrent assertion statement
// whose spec the evaluation's parse may give up: an assert in an always
// procedure (§16.14.6), a cover sequence there, an expect statement
// (§16.17), and a restrict property statement, which is not evaluated at
// all (§16.14.4).
TEST(PropertySpecGrammar, EveryStatementsSpecIsHeldToTheGrammar) {
  ExpectNotAdmitted("always @(posedge clk) assert property",
                    {{"a ##1\nb dist zz", 3}});
  ExpectNotAdmitted("always @(posedge clk) cover sequence",
                    {{"a\n|-> b ##1\nc dist zz", 3}});
  ExpectNotAdmitted("initial expect", {{"a ##1\nb dist zz", 3}});
  ExpectNotAdmitted("restrict property", {{"a ##1\nb dist zz", 3}});
}

// §16.11's subroutine call attached to a sequence of one boolean is a spec
// the grammar admits and the evaluation does not read, so each statement
// reports it as not evaluated and none reports a grammar error.
TEST(PropertySpecGrammar, AnAdmittedSpecIsReportedAsNotEvaluatedOnly) {
  const std::string kSpec = "@(posedge clk) (b, $display(\"m\"))";
  const std::vector<std::string> kStatements = {
      "assert property", "cover property", "cover sequence"};
  for (const std::string& statement : kStatements) {
    SCOPED_TRACE(statement);
    auto r = ParseSpec(statement, kSpec);
    EXPECT_TRUE(ReportedWarning(
        r.diags, "concurrent assertion is not evaluated", 2, "16.14"));
    EXPECT_FALSE(r.has_errors);
  }
  auto procedural = ParseSpec("always @(posedge clk) assert property", kSpec);
  EXPECT_TRUE(ReportedWarning(
      procedural.diags, "procedural concurrent assertion is not evaluated", 2,
      "16.14.6"));
  EXPECT_FALSE(procedural.has_errors);
}

}  // namespace
