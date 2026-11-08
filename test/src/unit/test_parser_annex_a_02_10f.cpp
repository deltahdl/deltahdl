#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kNotAdmitted = "is not one the grammar admits";

struct Malformed {
  const char* spec;
  uint32_t line;
};

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
          {"strong(a ##1 b) and weak(c) until\nd dist zz", 3},
          {"first_match(a ##1 b, x = 1) ##1\nc dist zz", 3},
          {"if (a) b else c ##1\nd dist zz", 3},
          {"(if (a) b) until\nc dist zz", 3},
          {"(if (a) b else c) until\nd dist zz", 3},
          {"(case (s) 1, 2: a; default: b; endcase) until\nc dist zz", 3},
          {"(a, x = 1, y += 2, z++, ++w, --v, $display(\"m\"), f(q), g, "
           "obj.m) ##1\nb dist zz",
           3},
          {"pkg::s(a ##1 b) and top.u.s(a ##1 b) ##1\nc dist zz", 3},
          {"s(, a ##1 b, $, posedge clk iff en or negedge rst, , "
           ".p(c ##1 d), .q()) ##1\nc dist zz",
           3},
          {"a[+] ##1 b[*] ##1 c[*2] ##1 d[->1:3] ##1 e[=2] ##1\nf dist zz", 3},
          {"s(a ##1 b)[*2] ##1\nc dist zz", 3},
      });
}

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
                        {"##[1:2\nb ##1\nc dist zz", 3},
                        {"##1\n] ##1\nb dist zz", 3},
                        {"a ##1 @(posedge clk\n] b ##1\nc dist zz", 3},
                        {"a ##1 @(posedge clk)\n] ##1\nc dist zz", 3},
                    });
}

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
                        {"(a ##1 b, c[0]\n) ##1\nd dist zz", 3},
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

TEST(PropertySpecGrammar, ACoverSequenceSpecAdmitsNoPropertyOperator) {
  ExpectNotAdmitted(
      "cover sequence",
      {
          {"@(posedge clk) first_match(a ##1 b) and c ##1\nd dist zz", 3},
          {"a\n|-> b ##1\nc dist zz", 3},
          {"a ##1\nnot b ##1\nc dist zz", 3},
      });
}

TEST(PropertySpecGrammar, EveryStatementsSpecIsHeldToTheGrammar) {
  ExpectNotAdmitted("always @(posedge clk) assert property",
                    {{"a ##1\nb dist zz", 3}});
  ExpectNotAdmitted("always @(posedge clk) cover sequence",
                    {{"a\n|-> b ##1\nc dist zz", 3}});
  ExpectNotAdmitted("initial expect", {{"a ##1\nb dist zz", 3}});
  ExpectNotAdmitted("restrict property", {{"a ##1\nb dist zz", 3}});
}

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

constexpr const char* kPropertyForSequence =
    "a property stands where the grammar admits only a sequence";
constexpr const char* kSequenceForBoolean =
    "a sequence stands where the grammar admits only an expression_or_dist";

void ExpectMisplaced(const char* message, const std::vector<Malformed>& cases) {
  for (const Malformed& c : cases) {
    SCOPED_TRACE(c.spec);
    auto r = ParseSpec("assert property", c.spec);
    EXPECT_TRUE(ReportedError(r.diags, message, c.line, "A.2.10"));
  }
}

TEST(PropertySpecGrammar, AnImplicationTakesASequenceOnItsLeft) {
  ExpectMisplaced(kPropertyForSequence,
                  {
                      {"@(posedge clk)\n(a |-> b) |-> c ##1\nd dist zz", 3},
                      {"@(posedge clk)\nnot a #=# b ##1\nc dist zz", 3},
                  });
}

TEST(PropertySpecGrammar, StrongWeakAndFirstMatchTakeASequence) {
  ExpectMisplaced(kPropertyForSequence,
                  {
                      {"strong(\na |-> b) ##1\nc dist zz", 3},
                      {"weak(\nnexttime a) ##1\nb dist zz", 3},
                      {"first_match(\na until b, x = 1) ##1\nc dist zz", 3},
                  });
}

TEST(PropertySpecGrammar, ASequenceOperatorTakesSequences) {
  ExpectMisplaced(
      kPropertyForSequence,
      {
          {"@(posedge clk)\n(not a) ##1 b ##1\nc dist zz", 3},
          {"a ##1\n(b implies c) ##1\nd dist zz", 3},
          {"##1\n(always a) ##1\nb dist zz", 3},
          {"@(posedge clk)\n(a |=> b) intersect c ##1\nd dist zz", 3},
          {"a within\n(b |-> c) or\nd dist zz", 3},
          {"x ##1\n(a |-> b)[*2] ##1\nc dist zz", 3},
          {"(\na |-> b, x = 1) ##1\nc dist zz", 3},
      });
}

TEST(PropertySpecGrammar, ThroughoutTakesAnExpressionOnItsLeft) {
  ExpectMisplaced(kSequenceForBoolean,
                  {
                      {"x or\n(a ##1 b) throughout c ##1\nd dist zz", 3},
                      {"x or\na ##1 b throughout c ##1\nd dist zz", 3},
                  });
}

TEST(PropertySpecGrammar, AnOperandIsGroupedByPrecedence) {
  const std::vector<std::string> kSpecs = {
      "a |-> b |=> (c, $display(\"m\"))",
      "nexttime a ##1 b and (c, $display(\"m\"))",
      "nexttime [2] a and (b, $display(\"m\"))",
      "s_always [1:2] a and (b, $display(\"m\"))",
      "accept_on (r) a or (b, $display(\"m\"))",
      "not a and (b, $display(\"m\"))",
      "(a, $display(\"m\")) or b |-> c",
      "s(a ##1 b) and (c, $display(\"m\")) |-> d",
      "a throughout b ##1 c or (d, $display(\"m\"))",
      "always a ##1 b or (c, $display(\"m\")) |-> d",
      "strong(a ##1 b) until c or (d, $display(\"m\"))",
  };
  for (const std::string& spec : kSpecs) {
    SCOPED_TRACE(spec);
    auto r = ParseSpec("assert property", "@(posedge clk) " + spec);
    EXPECT_TRUE(ReportedWarning(
        r.diags, "concurrent assertion is not evaluated", 2, "16.14"));
    EXPECT_FALSE(r.has_errors);
  }
}

}  // namespace
