#include "fixture_parser.h"
#include "helpers_concurrent_assertion_types.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  assert property (a |-> b)\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyMissingOpenParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  assert property a |-> b);\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyMissingCloseParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  assert property (a |-> b;\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorAssertPropertyMissingPropertyKw) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  assert (a |-> b);\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorAssumePropertyMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  assume property (a |-> b)\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorAssumePropertyMissingCloseParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  assume property (a |-> b;\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorCoverPropertyMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  cover property (a |-> b)\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorCoverPropertyMissingCloseParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  cover property (a |-> b;\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorCoverSequenceMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  cover sequence (a ##1 b)\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorCoverSequenceMissingCloseParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  cover sequence (a ##1 b;\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorRestrictPropertyMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  restrict property (a |-> b)\n"
              "endmodule\n"));
}

TEST(ConcurrentAssertionParsing, ErrorRestrictPropertyMissingCloseParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  restrict property (a |-> b;\n"
              "endmodule\n"));
}

TEST(PropertyDeclParsing, ErrorMissingEndproperty) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    a |-> b;\n"
              "endmodule\n"));
}

TEST(PropertyDeclParsing, ErrorMissingPropertyName) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  property;\n"
              "    a |-> b;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(PropertyDeclParsing, ErrorMismatchedEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    a |-> b;\n"
      "  endproperty : p2\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PropertyDeclParsing, ErrorMissingSemicolonAfterName) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  property p\n"
              "    a |-> b;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(PropertyDeclParsing, ErrorUnclosedPortList) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  property p(a, b;\n"
              "    a |-> b;\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(SequenceDeclParsing, ErrorMissingEndsequence) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  sequence s;\n"
              "    a ##1 b;\n"
              "endmodule\n"));
}

TEST(SequenceDeclParsing, ErrorMissingSequenceName) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  sequence;\n"
              "    a ##1 b;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(SequenceDeclParsing, ErrorMismatchedEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  sequence s1;\n"
      "    a ##1 b;\n"
      "  endsequence : s2\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SequenceDeclParsing, ErrorMissingSemicolonAfterName) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  sequence s\n"
              "    a ##1 b;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(SequenceDeclParsing, ErrorUnclosedPortList) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  sequence s(a, b;\n"
              "    a ##1 b;\n"
              "  endsequence\n"
              "endmodule\n"));
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

// property_lvar_port_direction ::= input
// A property port may carry `local`, optionally followed by `input`, but
// no other direction is permitted.
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
  EXPECT_TRUE(r.has_errors);
}

TEST(PropertyDeclParsing, PropertyPortLocalInoutRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p(local inout logic x);\n"
      "    x;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// 'output' or 'inout' inside a property port list is illegal even
// without a preceding 'local' — the only legal direction is 'input'
// and it must follow 'local'.
TEST(PropertyDeclParsing, PropertyPortOutputWithoutLocalRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p(output logic x);\n"
      "    x;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PropertyDeclParsing, PropertyPortInoutWithoutLocalRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p(inout logic x);\n"
      "    x;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PropertyDeclParsing, PropertyPortInputWithoutLocalRejected) {
  auto r = Parse(
      "module m;\n"
      "  property p(input logic x);\n"
      "    x;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// expect_property_statement ::= expect ( property_spec ) action_block
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
  EXPECT_TRUE(Parse("module m;\n"
                    "  initial begin\n"
                    "    expect (a |-> b ;\n"
                    "  end\n"
                    "endmodule\n")
                  .has_errors);
}

// property_formal_type ::= sequence_formal_type | property
// sequence_formal_type ::= data_type_or_implicit | sequence | untyped
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

// sequence_lvar_port_direction ::= input | inout | output
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

// property_spec ::= [ clocking_event ] [ disable iff ( expression_or_dist ) ]
//                   property_expr
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

// property_expr alternatives (parser skips body but must remain balanced).
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

// sequence_expr alternatives (parser skips body but must remain balanced).
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

// cycle_delay_range ::= ## constant_primary
//                    |  ## [ cycle_delay_const_range_expression ]
//                    |  ##[*] | ##[+]
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

// boolean_abbrev / sequence_abbrev:
//   consecutive_repetition ::= [* const_or_range_expression ] | [*] | [+]
//   nonconsecutive_repetition ::= [= const_or_range_expression ]
//   goto_repetition ::= [-> const_or_range_expression ]
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

// assertion_variable_declaration ::= var_data_type
// list_of_variable_decl_assignments ;
TEST(SequenceDeclParsing, AssertionVariableDeclaration) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; logic v; v = 1; v ##1 a; endsequence\n"
              "endmodule\n"));
}

// property_case_item ::= expression_or_dist { , expression_or_dist } :
// property_expr ;
//                     |  default [ : ] property_expr ;
TEST(PropertyExprParsing, PropertyCaseItem) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    case (sel) 1: a; 2: b; default: c; endcase\n"
              "  endproperty\n"
              "endmodule\n"));
}

// sequence_instance ::= ps_or_hierarchical_sequence_identifier
//                       [ ( [ sequence_list_of_arguments ] ) ]
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

// sequence_list_of_arguments ::= ... { , . identifier ( [ sequence_actual_arg ]
// ) }
TEST(SequenceExprParsing, SequenceInstanceWithNamedArgs) {
  auto r = Parse(
      "module m;\n"
      "  property p; my_seq(.x(a), .y(b)); endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// sequence_actual_arg ::= event_expression | sequence_expr | $
TEST(SequenceExprParsing, SequenceActualArgDollar) {
  auto r = Parse(
      "module m;\n"
      "  property p; my_seq($); endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// property_instance ::= ps_or_hierarchical_property_identifier
//                       [ ( [ property_list_of_arguments ] ) ]
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

// sequence_method_call ::= sequence_instance . method_identifier
TEST(SequenceExprParsing, SequenceMethodCall) {
  auto r = Parse(
      "module m;\n"
      "  property p; my_seq.matched ##1 a; endproperty\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// sequence_match_item ::= operator_assignment | inc_or_dec_expression
//                      |  subroutine_call
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
