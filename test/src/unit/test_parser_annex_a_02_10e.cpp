#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_concurrent_assertion_types.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a |-> b)\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyMissingOpenParen) {
  auto r = Parse(
      "module m;\n"
      "  assert property a |-> b);\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got identifier", 2, "16.14"));
}

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a |-> b;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got EOF", 4, "16.14"));
}

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyMissingPropertyKw) {
  auto r = Parse(
      "module m;\n"
      "  assert (a |-> b);\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'property', got '('", 2, "16.14"));
}

TEST(ConcurrentAssertionParsing, ErrorAssumePropertyMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  assume property (a |-> b)\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

TEST(ConcurrentAssertionParsing, ErrorAssumePropertyMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  assume property (a |-> b;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got EOF", 4, "16.14"));
}

TEST(ConcurrentAssertionParsing, ErrorCoverPropertyMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  cover property (a |-> b)\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

TEST(ConcurrentAssertionParsing, ErrorCoverPropertyMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  cover property (a |-> b;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got EOF", 4, "16.14.3"));
}

TEST(ConcurrentAssertionParsing, ErrorCoverSequenceMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (a ##1 b)\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

TEST(ConcurrentAssertionParsing, ErrorCoverSequenceMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (a ##1 b;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got EOF", 4, "16.14.3"));
}

TEST(ConcurrentAssertionParsing, ErrorRestrictPropertyMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (a |-> b)\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "16.14.4"));
}

TEST(ConcurrentAssertionParsing, ErrorRestrictPropertyMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (a |-> b;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got EOF", 4, "16.14.4"));
}

TEST(PropertyDeclParsing, ErrorMissingEndproperty) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    a |-> b;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endproperty', got EOF", 5, "16.12"));
}

TEST(PropertyDeclParsing, ErrorMissingPropertyName) {
  auto r = Parse(
      "module m;\n"
      "  property;\n"
      "    a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 2, "16.12"));
}

TEST(PropertyDeclParsing, ErrorMismatchedEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    a |-> b;\n"
      "  endproperty : p2\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "end label 'p2' does not match 'p1'", 4, "9.3.4"));
}

TEST(PropertyDeclParsing, ErrorMissingSemicolonAfterName) {
  auto r = Parse(
      "module m;\n"
      "  property p\n"
      "    a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got identifier", 3, "16.12"));
}

TEST(PropertyDeclParsing, ErrorUnclosedPortList) {
  auto r = Parse(
      "module m;\n"
      "  property p(a, b;\n"
      "    a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got EOF", 6, "16.12"));
}

TEST(SequenceDeclParsing, ErrorMissingEndsequence) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    a ##1 b;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endsequence', got EOF", 5, "16.8"));
}

TEST(SequenceDeclParsing, ErrorMissingSequenceName) {
  auto r = Parse(
      "module m;\n"
      "  sequence;\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 2, "16.8"));
}

TEST(SequenceDeclParsing, ErrorMismatchedEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  sequence s1;\n"
      "    a ##1 b;\n"
      "  endsequence : s2\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "end label 's2' does not match 's1'", 4, "9.3.4"));
}

TEST(SequenceDeclParsing, ErrorMissingSemicolonAfterName) {
  auto r = Parse(
      "module m;\n"
      "  sequence s\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got identifier", 3, "16.8"));
}

TEST(SequenceDeclParsing, ErrorUnclosedPortList) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(a, b;\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got EOF", 6, "16.8"));
}

TEST(PropertyDeclParsing, MultiplePropertyDecls) {
  auto r = Parse(
      "module m;\n"
      "  property p1; a; endproperty\n"
      "  property p2; b; endproperty\n"
      "  property p3; c; endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kPropertyDecl),
      3u);
}

TEST(SequenceDeclParsing, MultipleSequenceDecls) {
  auto r = Parse(
      "module m;\n"
      "  sequence s1; a; endsequence\n"
      "  sequence s2; b; endsequence\n"
      "  sequence s3; c; endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl),
      3u);
}

TEST(ConcurrentAssertionParsing, AllFiveAssertionTypes) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a);\n"
      "  assume property (b);\n"
      "  cover property (c);\n"
      "  cover sequence (d);\n"
      "  restrict property (e);\n"
      "endmodule\n");
  VerifyAllFiveConcurrentAssertionTypes(r);
}

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert property (a |-> b);\n"
      "  end\n"
      "endmodule\n");

  ASSERT_NE(r.cu, nullptr);
}

TEST(ConcurrentAssertionParsing, AssertPropertyWithElseActionBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (a |-> b)\n"
              "    $display(\"pass\");\n"
              "  else\n"
              "    $error(\"fail\");\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, AssertPropertyWithPassActionOnly) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (a |-> b)\n"
              "    $display(\"pass\");\n"
              "endmodule\n"));
}

TEST(PropertyDeclParsing, PropertyPortLocalInputOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(local input logic x);\n"
              "    x;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(PropertyDeclParsing, PropertyPortLocalOnlyOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(local logic x);\n"
              "    x;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(PropertyDeclParsing, PropertyPortLocalOutputRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p(local output logic x);\n"
      "    x;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "property port direction must be 'input'",
                            2, "16.12.19"));
}

TEST(PropertyDeclParsing, PropertyPortLocalInoutRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p(local inout logic x);\n"
      "    x;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "property port direction must be 'input'",
                            2, "16.12.19"));
}

TEST(PropertyDeclParsing, PropertyPortOutputWithoutLocalRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p(output logic x);\n"
      "    x;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "property port direction must be 'input'",
                            2, "16.12.19"));
}

TEST(PropertyDeclParsing, PropertyPortInoutWithoutLocalRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p(inout logic x);\n"
      "    x;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "property port direction must be 'input'",
                            2, "16.12.19"));
}

TEST(PropertyDeclParsing, PropertyPortInputWithoutLocalRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p(input logic x);\n"
      "    x;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "property port direction 'input' requires 'local'",
                            2, "16.12.19"));
}

TEST(ExpectStatementParsing, MinimalExpect) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    expect (a |-> b);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpectStatementParsing, ExpectWithActionBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    expect (a |-> b) $display(\"ok\");\n"
              "    else $error(\"fail\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ExpectStatementParsing, ExpectMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    expect (a |-> b ;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 6, "11.2"));
}

TEST(PropertyDeclParsing, PropertyPortFormalTypeProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(property q);\n"
              "    q;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(PropertyDeclParsing, PropertyPortFormalTypeSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(sequence s);\n"
              "    s |-> 1;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(PropertyDeclParsing, PropertyPortFormalTypeUntyped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(untyped x);\n"
              "    x;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(SequenceDeclParsing, SequencePortLocalInput) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local input logic x);\n"
              "    x;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(SequenceDeclParsing, SequencePortLocalInout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local inout logic x);\n"
              "    x;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(SequenceDeclParsing, SequencePortLocalOutput) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local output logic x);\n"
              "    x;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(PropertySpecParsing, ClockingEventOnly) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a |-> b);\n"
              "endmodule\n"));
}

TEST(PropertySpecParsing, DisableIffOnly) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (disable iff (rst) a |-> b);\n"
              "endmodule\n"));
}

TEST(PropertySpecParsing, ClockingEventAndDisableIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) disable iff (rst) a |-> b);\n"
              "endmodule\n"));
}

TEST(PropertyExprParsing, NotPropertyExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; not a; endproperty\n"
              "endmodule\n"));
}

TEST(PropertyExprParsing, StrongSequenceExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; strong (a ##1 b); endproperty\n"
              "endmodule\n"));
}

TEST(PropertyExprParsing, WeakSequenceExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; weak (a ##1 b); endproperty\n"
              "endmodule\n"));
}

TEST(PropertyExprParsing, NexttimePropertyExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; nexttime a; endproperty\n"
              "endmodule\n"));
}

TEST(PropertyExprParsing, AlwaysPropertyExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; always a; endproperty\n"
              "endmodule\n"));
}

TEST(PropertyExprParsing, EventuallyPropertyExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; s_eventually a; endproperty\n"
              "endmodule\n"));
}

TEST(PropertyExprParsing, UntilPropertyExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; a until b; endproperty\n"
              "endmodule\n"));
}

TEST(PropertyExprParsing, IffPropertyExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; a iff b; endproperty\n"
              "endmodule\n"));
}

TEST(PropertyExprParsing, AcceptOnPropertyExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p; accept_on (rst) a; endproperty\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, ConcatenationWithCycleDelay) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b ##2 c; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, AndComposition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a and b; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, IntersectComposition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a intersect b; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, OrComposition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a or b; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, ThroughoutComposition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a throughout (b ##1 c); endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, WithinComposition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a within b; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, FirstMatch) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; first_match(a ##1 b); endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, CycleDelayRangeBounded) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##[1:3] b; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, CycleDelayRangeOpenEnded) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##[1:$] b; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, CycleDelayRangeStar) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##[*] b; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, CycleDelayRangePlus) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##[+] b; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, ConsecutiveRepetitionConstant) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a [*3]; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, ConsecutiveRepetitionStar) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a [*]; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, ConsecutiveRepetitionPlus) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a [+]; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, NonconsecutiveRepetition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a [= 3]; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, GotoRepetition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a [-> 2]; endsequence\n"
              "endmodule\n"));
}

TEST(SequenceDeclParsing, AssertionVariableDeclaration) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; logic v; (a, v = 1) ##1 v; endsequence\n"
              "endmodule\n"));
}

TEST(PropertyExprParsing, PropertyCaseItem) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    case (sel) 1: a; 2: b; default: c; endcase\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(SequenceExprParsing, SequenceInstanceWithoutArguments) {
  auto r = Parse(
      "module m;\n"
      "  property p; my_seq; endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExprParsing, SequenceInstanceWithPositionalArgs) {
  auto r = Parse(
      "module m;\n"
      "  property p; my_seq(a, b); endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExprParsing, SequenceInstanceWithNamedArgs) {
  auto r = Parse(
      "module m;\n"
      "  property p; my_seq(.x(a), .y(b)); endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExprParsing, SequenceActualArgDollar) {
  auto r = Parse(
      "module m;\n"
      "  property p; my_seq($); endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(PropertyExprParsing, PropertyInstanceWithoutArguments) {
  auto r = Parse(
      "module m;\n"
      "  property outer; nested_prop; endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(PropertyExprParsing, PropertyInstanceWithArguments) {
  auto r = Parse(
      "module m;\n"
      "  property outer; nested_prop(a, b); endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExprParsing, SequenceMethodCall) {
  auto r = Parse(
      "module m;\n"
      "  property p; my_seq.matched ##1 a; endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExprParsing, SequenceMatchItemPostIncrement) {
  auto r = Parse(
      "module m;\n"
      "  sequence s; (a, count++) ##1 b; endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExprParsing, SequenceMatchItemAssignment) {
  auto r = Parse(
      "module m;\n"
      "  sequence s; (a, count = count + 1) ##1 b; endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExprParsing, SequenceMatchItemSubroutineCall) {
  auto r = Parse(
      "module m;\n"
      "  sequence s; (a, $display(\"hit\")) ##1 b; endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
