// §11.12: Let construct

#include "fixture_parser.h"

using namespace delta;

namespace {

// let_declaration in function body
TEST(ParserA28, LetDeclInFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void foo();\n"
              "    let inc(x) = x + 1;\n"
              "  endfunction\n"
              "endmodule\n"));
}

// =============================================================================
// A.2.12 Production #1: let_declaration
// let_declaration ::= let let_identifier [ ( [ let_port_list ] ) ] = expression
// ;
// =============================================================================
TEST(ParserA212, LetDecl_NoArgs) {
  auto r = Parse(
      "module m;\n"
      "  let addr = base + offset;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "addr");
}

TEST(ParserA212, LetDecl_EmptyParens) {
  auto r = Parse(
      "module m;\n"
      "  let my_val() = 42;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "my_val");
  EXPECT_TRUE(item->func_args.empty());
}

TEST(ParserA212, LetDecl_WithArgs) {
  auto r = Parse(
      "module m;\n"
      "  let op(x, y, z) = |((x | y) & z);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "op");
  ASSERT_EQ(item->func_args.size(), 3u);
}

TEST(ParserA212, LetDecl_HasBodyExpr) {
  auto r = Parse(
      "module m;\n"
      "  let sum(a, b) = a + b;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserA212, LetDecl_ComplexExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let max(a, b) = (a > b) ? a : b;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetDecl_InPackage) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  let my_op(x, y) = x & y;\n"
              "endpackage\n"));
}

TEST(ParserA212, LetDecl_InInterface) {
  EXPECT_TRUE(
      ParseOk("interface ifc;\n"
              "  let bus_ok(req, ack) = req & ack;\n"
              "endinterface\n"));
}

TEST(ParserA212, LetDecl_InProgram) {
  EXPECT_TRUE(
      ParseOk("program p;\n"
              "  let tval(x) = x + 1;\n"
              "endprogram\n"));
}

TEST(ParserA212, LetDecl_InChecker) {
  EXPECT_TRUE(
      ParseOk("checker chk;\n"
              "  let valid(a, b) = a | b;\n"
              "endchecker\n"));
}

TEST(ParserA212, LetDecl_AsBlockItem) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    let local_add(a, b) = a + b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetDecl_Multiple) {
  auto r = Parse(
      "module m;\n"
      "  let add(a, b) = a + b;\n"
      "  let sub(a, b) = a - b;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kLetDecl) count++;
  }
  EXPECT_EQ(count, 2);
}

// =============================================================================
// A.2.12 Production #2: let_identifier
// let_identifier ::= identifier
// =============================================================================
TEST(ParserA212, LetIdentifier_Simple) {
  auto r = Parse(
      "module m;\n"
      "  let foo = 1;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "foo");
}

// =============================================================================
// A.2.12 Production #3: let_port_list
// let_port_list ::= let_port_item { , let_port_item }
// =============================================================================
TEST(ParserA212, LetPortList_Single) {
  auto r = Parse(
      "module m;\n"
      "  let f(x) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(ParserA212, LetPortList_Multiple) {
  auto r = Parse(
      "module m;\n"
      "  let f(a, b, c, d) = a + b + c + d;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 4u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[1].name, "b");
  EXPECT_EQ(item->func_args[2].name, "c");
  EXPECT_EQ(item->func_args[3].name, "d");
}

TEST(ParserA212, LetPortList_MixedTypes) {
  auto r = Parse(
      "module m;\n"
      "  let f(logic [7:0] a, int b, c) = a + b + c;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 3u);
}

// =============================================================================
// A.2.12 Production #4: let_port_item
// let_port_item ::= {attribute_instance} let_formal_type
//     formal_port_identifier {variable_dimension} [= expression]
// =============================================================================
TEST(ParserA212, LetPortItem_ImplicitType) {
  auto r = Parse(
      "module m;\n"
      "  let f(x) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
}

// =============================================================================
// A.2.12 Production #5: let_formal_type
// let_formal_type ::= data_type_or_implicit | untyped
// =============================================================================
TEST(ParserA212, LetFormalType_Untyped) {
  auto r = Parse(
      "module m;\n"
      "  let f(untyped a) = a;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "a");
}

// =============================================================================
// A.2.12 Production #6: let_expression
// let_expression ::= [package_scope] let_identifier
//     [ ( [ let_list_of_arguments ] ) ]
// =============================================================================
TEST(ParserA212, LetExpr_SimpleCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let op(x, y) = x + y;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = op(3, 4);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
