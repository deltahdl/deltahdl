#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

constexpr const char* kNotAdmitted = "is not one the grammar admits";

// A.2.10's assertion_variable_declaration is `var_data_type
// list_of_variable_decl_assignments ;`, and A.2.2.1's var_data_type is a
// data_type or `var` before a data_type_or_implicit, a data_type naming a type
// through a package or class scope among them. Each declaration below
// declares its variable as a local of the sequence (§16.10), and the type
// name's scope is read with it rather than as further variables.
TEST(AssertionVariableDeclParsing, VarAndScopedTypesDeclareSequenceLocals) {
  auto r = Parse(
      "package P;\n"
      "  typedef logic [7:0] word_t;\n"
      "endpackage\n"
      "class C #(int W = 8);\n"
      "  typedef logic [W-1:0] t;\n"
      "endclass\n"
      "module m(input logic clk, a, b);\n"
      "  typedef logic [3:0] nib_t;\n"
      "  sequence s;\n"
      "    var int n;\n"
      "    var v;\n"
      "    var signed [3:0] sv;\n"
      "    var nib_t vn;\n"
      "    P::word_t w;\n"
      "    P::word_t [1:0] pw;\n"
      "    C#(4)::t c;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  const std::vector<std::string_view> kNames = {"n", "v",  "sv", "vn",
                                                "w", "pw", "c"};
  EXPECT_EQ(item->prop_seq_assert_vars, kNames);
  const auto& locals = item->seq_linear.locals;
  ASSERT_EQ(locals.size(), kNames.size());
  EXPECT_EQ(locals[0].type_kw, TokenKind::kKwInt);
  EXPECT_EQ(locals[1].type_kw, TokenKind::kKwLogic);
  EXPECT_EQ(locals[2].type_kw, TokenKind::kKwLogic);
  EXPECT_EQ(locals[2].signing, TokenKind::kKwSigned);
  EXPECT_EQ(locals[3].named_type.type_name, "nib_t");
  EXPECT_EQ(locals[4].named_type.type_name, "word_t");
  EXPECT_EQ(locals[4].named_type.scope_name, "P");
  EXPECT_EQ(locals[5].packed_dims.size(), 1u);
  EXPECT_EQ(locals[6].named_type.scope_name, "C");
}

// The same declarations at the head of a property's body, and a body that
// opens with a constant named through a package's scope, which declares
// nothing.
TEST(AssertionVariableDeclParsing, VarAndScopedTypesDeclarePropertyLocals) {
  auto r = Parse(
      "package P;\n"
      "  typedef logic [7:0] word_t;\n"
      "  parameter logic K = 1;\n"
      "endpackage\n"
      "module m(input logic clk, a);\n"
      "  property q;\n"
      "    var logic [3:0] k;\n"
      "    P::word_t w;\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "  sequence s;\n"
      "    P::K ##1 a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* property = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(property, nullptr);
  const std::vector<std::string_view> kNames = {"k", "w"};
  EXPECT_EQ(property->prop_seq_assert_vars, kNames);
  auto* sequence = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(sequence, nullptr);
  EXPECT_TRUE(sequence->prop_seq_assert_vars.empty());
}

// §16.10 with §16.6 rules chandle out as a local's type whether or not
// `var` is written before it.
TEST(AssertionVariableDeclParsing, ChandleAfterVarIsReported) {
  auto r = Parse(
      "module m(input logic clk, a);\n"
      "  sequence s;\n"
      "    var chandle h;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "an assertion variable may not be declared of type chandle", 3,
      "16.10"));
}

// A scope with no name after it, and a packed dimension the source ends in,
// end the reading of a declaration's type rather than running past the
// tokens there are, and what is left of the body is no sequence_expr.
TEST(AssertionVariableDeclParsing, ATruncatedTypeEndsTheDeclaration) {
  auto scope = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    P::;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(scope.diags, kNotAdmitted, 3, "A.2.10"));
  auto dimension = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    int [3");
  EXPECT_TRUE(ReportedError(dimension.diags, kNotAdmitted, 3, "A.2.10"));
}

// A.2.10's property_port_item and sequence_port_item each name one
// formal_port_identifier, after which only variable dimensions and a default
// stand. An item with no formal, a trailing comma's empty item, a token
// after a formal that is none of those, and a parenthesized group standing
// where an item would are reported; an empty list, a dimension and a default
// are not.
void ExpectPortItemsHeldToTheirShape(const char* port, const char* end) {
  SCOPED_TRACE(port);
  const std::string kPort = port;
  auto r = Parse("module m(input logic a, b);\n  " + kPort +
                 " p1(int, b);\n    b;\n  " + end + "\n  " + kPort +
                 " p2(int x y);\n    x;\n  " + end + "\n  " + kPort +
                 " p3(a, );\n    a;\n  " + end + "\n  " + kPort +
                 " p4();\n    a;\n  " + end + "\n  " + kPort +
                 " p5(int x [2][3], y = 1);\n    x == y;\n  " + end + "\n  " +
                 kPort + " p6((a));\n    a;\n  " + end + "\nendmodule\n");
  const std::string kNoFormal =
      kPort + " port item names a formal_port_identifier";
  const std::string kStray = kPort +
                             " port item takes only variable dimensions and "
                             "a default after its formal";
  EXPECT_TRUE(ReportedError(r.diags, kNoFormal, 2, "A.2.10"));
  EXPECT_TRUE(ReportedError(r.diags, kStray, 5, "A.2.10"));
  EXPECT_TRUE(ReportedError(r.diags, kNoFormal, 8, "A.2.10"));
  EXPECT_TRUE(ReportedError(r.diags, kNoFormal, 17, "A.2.10"));
  for (uint32_t line : {11u, 14u}) {
    EXPECT_FALSE(ReportedError(r.diags, kNoFormal, line, "A.2.10"));
    EXPECT_FALSE(ReportedError(r.diags, kStray, line, "A.2.10"));
  }
}

TEST(AssertionPortItemParsing, PropertyPortItemsAreHeldToTheirShape) {
  ExpectPortItemsHeldToTheirShape("property", "endproperty");
}

TEST(AssertionPortItemParsing, SequencePortItemsAreHeldToTheirShape) {
  ExpectPortItemsHeldToTheirShape("sequence", "endsequence");
}

// Attribute instances may open a port item and name no formal, so the
// formals are the identifiers the items name after them.
void ExpectAttributesReadPast(const char* port, const char* end,
                              ModuleItemKind kind) {
  SCOPED_TRACE(port);
  auto r = Parse(std::string("module m(input logic a);\n  ") + port +
                 " q((* keep *) int x, (* mark = 1, tag *) y);\n    x == y;\n"
                 "  " +
                 end + "\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, kind);
  ASSERT_NE(item, nullptr);
  const std::vector<std::string_view> kFormals = {"x", "y"};
  EXPECT_EQ(item->prop_formals, kFormals);
  auto truncated = Parse(std::string("module m;\n  ") + port + " q((* keep");
  EXPECT_TRUE(ReportedError(truncated.diags, kNotAdmitted, 2, "A.2.10"));
}

TEST(AssertionPortItemParsing, PropertyPortAttributesAreReadPast) {
  ExpectAttributesReadPast("property", "endproperty",
                           ModuleItemKind::kPropertyDecl);
}

TEST(AssertionPortItemParsing, SequencePortAttributesAreReadPast) {
  ExpectAttributesReadPast("sequence", "endsequence",
                           ModuleItemKind::kSequenceDecl);
}

// A.2.10's property_list_of_arguments and sequence_list_of_arguments are
// positional actuals, any of them empty, then named ones, or named ones from
// the first; a named actual's own actual is never named. Each instance below
// breaks that on line 3, a trailing comma's empty actual after a named one
// among them, whether it is read as a property instance whose actual is a
// sequence, as a sequence instance of a sequence_expr, or by the grammar's
// own scan.
TEST(InstanceArgumentListParsing, APositionalActualAfterANamedOneIsReported) {
  const char* const kSpecs[] = {
      "p(.x(a ##1 b),\nc)", "s(.x(a),\nb) ##1 c",   "p(.x(a ##1 b),\n)",
      "s(.x(a),\n) ##1 c",  "p(.x(\n.y(a ##1 b)))",
  };
  for (const char* spec : kSpecs) {
    SCOPED_TRACE(spec);
    auto r = Parse(std::string("module m(input logic clk, a, b, c);\n"
                               "  assert property (@(posedge clk) ") +
                   spec + ");\nendmodule\n");
    EXPECT_TRUE(ReportedError(r.diags, kNotAdmitted, 3, "A.2.10"));
  }
}

// The lists the productions admit: named actuals one after another, empty
// positional ones, an empty named one, and positional ones before a named
// one. Each list holds a sequence, which no expression reads, and the match
// item's subroutine call makes the evaluation's parse give the spec up, so
// the grammar's scan reads every list as an instance's.
TEST(InstanceArgumentListParsing, ListsTheProductionsWriteAreAccepted) {
  auto r = Parse(
      "module m(input logic clk, a, b, c);\n"
      "  assert property (@(posedge clk) p(.x(a ##1 b), .y(c)));\n"
      "  assert property (@(posedge clk) p(, a ##1 b) ##1 q(a ##1 b, )\n"
      "                   ##1 r(.x(), .y(a ##1 b)) ##1 t(a ##1 b, .y(c))\n"
      "                   ##1 (b, $display(\"m\")));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// A cover sequence statement's spec is a sequence_expr after its clock and
// disable condition, so a property operator in it is reported whether or not
// the evaluation's parse, which reads a property spec, reads it; a sequence
// draws no report.
TEST(CoverSequenceParsing, APropertyOperatorInTheSpecIsReported) {
  auto r = Parse(
      "module m(input logic clk, a, b);\n"
      "  cover sequence (@(posedge clk) a |-> b);\n"
      "  cover sequence (@(posedge clk) not a);\n"
      "  cover sequence (@(posedge clk) strong(a ##1 b));\n"
      "  initial cover sequence (@(posedge clk) a until b);\n"
      "  cover sequence (@(posedge clk) disable iff (b) a ##1 b);\n"
      "  initial cover sequence (@(posedge clk) a ##[1:2] b);\n"
      "endmodule\n");
  for (uint32_t line : {2u, 3u, 4u, 5u}) {
    EXPECT_TRUE(ReportedError(r.diags, kNotAdmitted, line, "A.2.10"));
  }
  for (uint32_t line : {6u, 7u}) {
    EXPECT_FALSE(ReportedError(r.diags, kNotAdmitted, line, "A.2.10"));
  }
}

// A sequence declaration's body after its assertion variable declarations is
// A.2.10's sequence_expr, with the `;` that may end it: a property operator,
// a delay with no operand after it, two operands with no operator between
// them, a disable condition and an empty body are reported on their lines;
// a clocked body, one with no `;` and one after a declaration are not.
TEST(DeclarationBodyGrammar, ASequenceBodyIsHeldToSequenceExpr) {
  auto r = Parse(
      "module m(input logic clk, a, b);\n"
      "  sequence s1;\n    a |-> b;\n  endsequence\n"
      "  sequence s2;\n    a ##1;\n  endsequence\n"
      "  sequence s3;\n    a ##1 b a;\n  endsequence\n"
      "  sequence s4;\n    disable iff (b) a;\n  endsequence\n"
      "  sequence s5;\n  endsequence\n"
      "  sequence s6;\n    @(posedge clk) a ##1 b;\n  endsequence\n"
      "  sequence s7;\n    a ##1 b\n  endsequence\n"
      "  sequence s8;\n    int x;\n    (a, x = 1) ##1 b;\n  endsequence\n"
      "endmodule\n");
  for (uint32_t line : {3u, 6u, 9u, 12u, 15u}) {
    EXPECT_TRUE(ReportedError(r.diags, kNotAdmitted, line, "A.2.10"));
  }
  for (uint32_t line : {17u, 20u, 21u, 24u}) {
    EXPECT_FALSE(ReportedError(r.diags, kNotAdmitted, line, "A.2.10"));
  }
}

// A property declaration's body after its assertion variable declarations is
// A.2.10's property_spec, with the `;` that may end it: an implication with
// no consequent, one with a property on its left, two operands with no
// operator between them and an empty body are reported on their lines; a
// clocked, disabled body, a case and an if with no `;` are not.
TEST(DeclarationBodyGrammar, APropertyBodyIsHeldToPropertySpec) {
  auto r = Parse(
      "module m(input logic clk, a, b);\n"
      "  property p1;\n    @(posedge clk) a |->;\n  endproperty\n"
      "  property p2;\n    (a |-> b) |-> a;\n  endproperty\n"
      "  property p3;\n    a b;\n  endproperty\n"
      "  property p4;\n  endproperty\n"
      "  property p5;\n    @(posedge clk) disable iff (b) a |=> b;\n"
      "  endproperty\n"
      "  property p6;\n    case (a) 1'b1: b; default: a; endcase\n"
      "  endproperty\n"
      "  property p7;\n    if (a) b else a\n  endproperty\n"
      "endmodule\n");
  for (uint32_t line : {3u, 9u, 12u}) {
    EXPECT_TRUE(ReportedError(r.diags, kNotAdmitted, line, "A.2.10"));
  }
  EXPECT_TRUE(ReportedError(
      r.diags, "a property stands where the grammar admits only a sequence", 6,
      "A.2.10"));
  for (uint32_t line : {14u, 17u, 20u}) {
    EXPECT_FALSE(ReportedError(r.diags, kNotAdmitted, line, "A.2.10"));
  }
}

}  // namespace
