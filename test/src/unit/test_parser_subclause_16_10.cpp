#include <gtest/gtest.h>

#include <cstddef>
#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

// §16.10: an assertion_variable_declaration declares a local variable inside
// a sequence body. The parser harvests each declared name so later stages can
// resolve references and enforce flow rules.
TEST(LocalVariableParsing, AssertionVariableDeclInSequenceParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    int x;\n"
      "    @(posedge clk) (a, x = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "x");
}

// §16.10: a comma-separated list of identifiers with optional declaration
// assignments forms a single assertion_variable_declaration. Each identifier
// names a distinct local variable.
TEST(LocalVariableParsing, AssertionVariableDeclMultipleNames) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    logic u, v = a, w = v || b;\n"
      "    @(posedge clk) (a, u = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 3u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "u");
  EXPECT_EQ(item->prop_seq_assert_vars[1], "v");
  EXPECT_EQ(item->prop_seq_assert_vars[2], "w");
}

// §16.10 references §16.8.2: a local variable declared in an
// assertion_variable_declaration and a local variable formal argument are
// distinct kinds of "local variable" but the term applies to both. The parser
// records each kind independently so downstream rules can read either set.
TEST(LocalVariableParsing, SequenceWithBothLocalKindsRecordedSeparately) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local inout int v1);\n"
      "    bit guard;\n"
      "    @(posedge clk) (a, guard = 1'b1) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 1u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInout);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "guard");
}

// §16.10: an assertion_variable_declaration is also permitted inside a
// property declaration.
TEST(LocalVariableParsing, AssertionVariableDeclInPropertyParses) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    int x;\n"
      "    @(posedge clk) (valid_in, x = pipe_in) |-> ##5 (pipe_out1 == "
      "(x+1));\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "x");
}

// §16.10: a sequence body without any assertion_variable_declaration must
// leave the harvested list empty — false positives would mislead later stage
// flow analysis.
TEST(LocalVariableParsing, NoAssertionVariableMeansEmptyList) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->prop_seq_assert_vars.empty());
}

// §16.10 Syntax 16-13 / §16.6: the var_data_type of an
// assertion_variable_declaration may include a packed dimension. The parser
// skips past packed-dim tokens before walking the name list so the harvested
// names still match the declaration.
TEST(LocalVariableParsing, AssertionVariableDeclWithPackedDimension) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    bit [7:0] q;\n"
      "    @(posedge clk) (a, q = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "q");
}

// §16.10: a local variable declared in a sequence body may not be used in the
// body's clocking event expression. Here the body local `x` is named as the
// clock signal `@(posedge x)`, which the parser must reject.
TEST(LocalVariableParsing, LocalVariableInClockingEventIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    logic x;\n"
      "    @(posedge x) (a, x = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags,
      "local variable \"x\" may not be used in a clocking event expression", 4,
      "16.10"));
}

// §16.10: the companion accepting case — a body local variable that is only
// assigned/read in the sequence body (not named in the clocking event) is
// legal, so clocking on an ordinary signal must not trip the check.
TEST(LocalVariableParsing, LocalVariableNotInClockingEventParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    logic x;\n"
      "    @(posedge clk) (a, x = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "x");
}

// §16.10 Syntax 16-13 / §16.6: the var_data_type of an
// assertion_variable_declaration may carry a signing keyword (signed/unsigned)
// after the type keyword. The parser advances past that signing token while
// consuming the type prefix, so the declared name is still harvested.
TEST(LocalVariableParsing, AssertionVariableDeclWithSigning) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    logic signed x;\n"
      "    @(posedge clk) (a, x = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "x");
}

// §16.10: a declaration assignment defines the local variable's initial value.
// The initializer need not be constant, but a constant literal is an equally
// valid initializer form; the parser skips whatever initializer expression
// follows the '=' and still records the declared name. This is the
// accumulating-local shape `int x = 0;` from §16.10's own examples.
TEST(LocalVariableParsing, AssertionVariableDeclWithConstantInitializer) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    int x = 0;\n"
      "    @(posedge clk) (a, x = data) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 1u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "x");
}

// §16.10: several assertion_variable_declaration items may appear in sequence
// at the head of a body. Each decl line contributes its own names to the
// harvested local-variable list in source order.
TEST(LocalVariableParsing, MultipleAssertionVariableDeclLinesAccumulate) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    int x;\n"
      "    logic y;\n"
      "    bit z;\n"
      "    @(posedge clk) (a, x = data, y = 1'b1, z = 1'b0) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_assert_vars.size(), 3u);
  EXPECT_EQ(item->prop_seq_assert_vars[0], "x");
  EXPECT_EQ(item->prop_seq_assert_vars[1], "y");
  EXPECT_EQ(item->prop_seq_assert_vars[2], "z");
}

// §16.10 with §16.6: a local variable's type is one an assertion may use,
// which chandle is not, in a sequence's body and in a property's (#5740).
TEST(LocalVariableParsing, AChandleLocalVariableIsReported) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a;\n"
      "  sequence s; int n; chandle h; @(posedge clk) a; endsequence\n"
      "  property p; chandle h; @(posedge clk) a; endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  constexpr char kMessage[] =
      "an assertion variable may not be declared of type chandle";
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 3, "16.10"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 4, "16.10"));
}

// §16.10: a group's match items run once, at each match of its
// sequence_expr, so where the operand ending the group repeats, `(b[*2],
// x++)` or `(b[->2], x++)`, the items are kept off it and captured on a
// literal 1 fused to its end, as `b[*2] ##0 (1, x++)` writes them; an
// unrepeated operand keeps the items itself.
TEST(SequenceLocalVariableParsing,
     AGroupsItemsAfterARepeatedOperandStandApart) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  sequence s1; int x; @(posedge clk) a ##1 (b[*2], x++); endsequence\n"
      "  sequence s2; int x; @(posedge clk) a ##1 (b[->2], x++); endsequence\n"
      "  sequence s3; int x; @(posedge clk) a ##1 (b, x++); endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kSequenceDecl) continue;
    SCOPED_TRACE(item->name);
    const SeqLinearBody& body = item->seq_linear;
    const bool kFused = item->name != "s3";
    ASSERT_EQ(body.operands.size(), kFused ? 3u : 2u);
    EXPECT_EQ(body.match_items[1].size(), kFused ? 0u : 1u);
    if (!kFused) continue;
    EXPECT_EQ(body.match_items[2].size(), 1u);
    EXPECT_EQ(body.operands[2]->text, "1");
    EXPECT_EQ(body.delays[2].min, 0u);
    EXPECT_EQ(body.delays[2].max, 0u);
    EXPECT_EQ(body.repetitions[2].kind, SeqRepetition::Kind::kNone);
  }
}

// §16.10 with A.10 footnote 51: a match item's operator_assignment or
// inc_or_dec_expression writes a variable_lvalue, which may select within the
// local or name a member of it. Each form is captured with the group's
// operand, `lvar` naming the local and `target` keeping the select or member
// written; read as a bare name alone, the target left the group unparsed and
// the body without an operand to evaluate.
TEST(SequenceLocalVariableParsing, AMatchItemTargetMaySelectWithinTheLocal) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [3:0] hi, lo; } pair_t;\n"
      "  logic clk, a, b;\n"
      "  sequence s;\n"
      "    logic [7:0] v;\n"
      "    pair_t p;\n"
      "    @(posedge clk) (a, v[1] = b, p.hi += 2, ++v[3:2], p.lo[0]--, v = 0)"
      " ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  const SeqLinearBody& body = item->seq_linear;
  ASSERT_EQ(body.operands.size(), 2u);
  const std::vector<SeqMatchAssign>& items = body.match_items[0];
  struct Case {
    std::string_view lvar;
    TokenKind op;
    ExprKind target;
  };
  const Case kCases[] = {{"v", TokenKind::kEq, ExprKind::kSelect},
                         {"p", TokenKind::kPlusEq, ExprKind::kMemberAccess},
                         {"v", TokenKind::kPlusEq, ExprKind::kSelect},
                         {"p", TokenKind::kMinusEq, ExprKind::kSelect}};
  ASSERT_EQ(items.size(), 5u);
  for (size_t i = 0; i < 4; ++i) {
    SCOPED_TRACE(i);
    EXPECT_EQ(items[i].lvar, kCases[i].lvar);
    EXPECT_EQ(items[i].op, kCases[i].op);
    ASSERT_NE(items[i].target, nullptr);
    EXPECT_EQ(items[i].target->kind, kCases[i].target);
  }
  EXPECT_EQ(items[4].lvar, "v");
  EXPECT_EQ(items[4].target, nullptr);
}

}  // namespace
