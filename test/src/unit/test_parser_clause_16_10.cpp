#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

}  // namespace
