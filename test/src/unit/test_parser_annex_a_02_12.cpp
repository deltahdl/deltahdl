#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// A.2.12 let_declaration ::= let let_identifier = expression ;
// The simplest form: no port list, a single right-hand-side expression.
TEST(LetDeclParsing, LetDecl_NoPorts) {
  auto r = Parse(
      "module m;\n"
      "  let answer = 42;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kLetDecl);
  // A.2.12 let_identifier ::= identifier
  EXPECT_EQ(item->name, "answer");
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_TRUE(item->func_args.empty());
}

// A.2.12 let_declaration ::= let let_identifier ( ) = expression ;
// An empty parenthesized port list is permitted.
TEST(LetDeclParsing, LetDecl_EmptyPortList) {
  auto r = Parse(
      "module m;\n"
      "  let zero() = 1'b0;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "zero");
  EXPECT_TRUE(item->func_args.empty());
}

// A.2.12 let_port_item ::= ... let_formal_type formal_port_identifier ...
// A single typed formal: let_formal_type takes the data_type_or_implicit form.
TEST(LetDeclParsing, LetPortItem_TypedFormal) {
  auto r = Parse(
      "module m;\n"
      "  let half(int x) = x / 2;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
}

// A.2.12 let_formal_type ::= data_type_or_implicit | untyped
// The `untyped` alternative for a formal port.
TEST(LetDeclParsing, LetFormalType_Untyped) {
  auto r = Parse(
      "module m;\n"
      "  let same(untyped a) = a;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "a");
}

// A.2.12 let_formal_type ::= data_type_or_implicit (implicit form: the type
// is omitted entirely and only the formal identifier appears).
TEST(LetDeclParsing, LetFormalType_Implicit) {
  auto r = Parse(
      "module m;\n"
      "  let inc(a) = a + 1;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "a");
}

// A.2.12 let_port_list ::= let_port_item { , let_port_item }
// More than one comma-separated formal.
TEST(LetDeclParsing, LetPortList_Multiple) {
  auto r = Parse(
      "module m;\n"
      "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].name, "sel");
  EXPECT_EQ(item->func_args[1].name, "d0");
  EXPECT_EQ(item->func_args[2].name, "d1");
}

// A.2.12 let_port_item ::= ... formal_port_identifier { variable_dimension }
// ... A formal carrying an unpacked dimension.
TEST(LetDeclParsing, LetPortItem_VariableDimension) {
  auto r = Parse(
      "module m;\n"
      "  let pick(int x [4]) = x[0];\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_FALSE(item->func_args[0].unpacked_dims.empty());
}

// A.2.12 let_port_item ::= ... [ = expression ]
// A formal with a default value expression.
TEST(LetDeclParsing, LetPortItem_DefaultValue) {
  auto r = Parse(
      "module m;\n"
      "  let scaled(int x = 1) = x * 2;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

// A.2.12 let_port_item ::= { attribute_instance } let_formal_type ...
// An attribute instance preceding a formal.
TEST(LetDeclParsing, LetPortItem_WithAttribute) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* foo *) int x) = x;\n"
              "endmodule\n"));
}

// A.2.12 let_expression ::= let_identifier ( let_list_of_arguments )
// where let_list_of_arguments uses positional let_actual_arg entries; each
// let_actual_arg ::= expression.
TEST(LetDeclParsing, LetExpression_PositionalArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
              "  wire w;\n"
              "  assign w = mux(s, a + 1, b);\n"
              "endmodule\n"));
}

// A.2.12 let_expression ::= let_identifier (with no argument list at all).
TEST(LetDeclParsing, LetExpression_NoArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let answer = 42;\n"
              "  wire [7:0] w;\n"
              "  assign w = answer;\n"
              "endmodule\n"));
}

// A.2.12 let_list_of_arguments: the fully-named form
// . identifier ( [ let_actual_arg ] ) { , . identifier ( [ let_actual_arg ] ) }
TEST(LetDeclParsing, LetListOfArguments_AllNamed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
              "  wire w;\n"
              "  assign w = mux(.sel(s), .d0(a), .d1(b));\n"
              "endmodule\n"));
}

// A.2.12 let_list_of_arguments: positional entries followed by trailing
// named entries: let_actual_arg { , let_actual_arg } { , . identifier ( ... ) }
TEST(LetDeclParsing, LetListOfArguments_PositionalThenNamed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
              "  wire w;\n"
              "  assign w = mux(s, .d0(a), .d1(b));\n"
              "endmodule\n"));
}

// A.2.12 let_list_of_arguments: a named entry may omit its actual argument,
// since let_actual_arg is optional: . identifier ( ).
TEST(LetDeclParsing, LetListOfArguments_NamedEmptyArg) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
              "  wire w;\n"
              "  assign w = mux(.sel(s), .d0(), .d1(b));\n"
              "endmodule\n"));
}

// A.2.12 let_expression ::= [ package_scope ] let_identifier ( ... )
// A let invocation qualified by a package scope.
TEST(LetDeclParsing, LetExpression_PackageScope) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "  assign w = pkg::mux(s, a, b);\n"
              "endmodule\n"));
}

// A let_declaration may appear inside a procedural block
// (block_item_declaration).
TEST(LetDeclParsing, LetDecl_InProceduralBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    let twice(x) = x + x;\n"
              "  end\n"
              "endmodule\n"));
}

// A.2.12 let_port_item ::= ... formal_port_identifier { variable_dimension }
// ... The variable_dimension group repeats: a formal with two unpacked
// dimensions.
TEST(LetDeclParsing, LetPortItem_MultipleVariableDimensions) {
  auto r = Parse(
      "module m;\n"
      "  let first(int x [2][3]) = x[0][0];\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].unpacked_dims.size(), 2u);
}

// A.2.12 let_list_of_arguments, alternative 1: each positional entry is
// [ let_actual_arg ] and so may be omitted. This omits the leading positional
// actual (distinct from the named-tail omission tested above), exercising the
// optional-positional form of the first alternative.
TEST(LetDeclParsing, LetListOfArguments_PositionalEmptyArg) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
              "  wire w;\n"
              "  assign w = mux(, a, b);\n"
              "endmodule\n"));
}

// A.2.12 let_expression ::= [ package_scope ] let_identifier
// The package_scope prefix with no trailing argument list.
TEST(LetDeclParsing, LetExpression_PackageScopeNoArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire [7:0] w;\n"
              "  assign w = pkg::answer;\n"
              "endmodule\n"));
}

// Error recovery: a let_declaration without the required `= expression`.
TEST(LetDeclParsing, ErrorMissingAssignment) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  let bad(x);\n"
              "endmodule\n"));
}

// Error recovery: a let_declaration must end with a semicolon.
TEST(LetDeclParsing, ErrorMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  let bad = 1\n"
              "endmodule\n"));
}

}  // namespace
