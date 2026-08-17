#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TypeDeclParsing, TypedefBasic) {
  auto r = Parse("module m; typedef logic [7:0] byte_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "byte_t");
}

// The five ForwardTypedef* cases below cover the forward typedef forms
// listed in 6.18. test_parser_annex_a_02_01_03.cpp carries the matching
// cases for the forward_type alternatives of the A.2.1.3
// type_declaration production, named ForwardType*.
TEST(TypeDeclParsing, ForwardTypedefClass) {
  auto r = Parse("module m; typedef class my_class; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "my_class");
}

TEST(TypeDeclParsing, ForwardTypedefInterfaceClass) {
  auto r = Parse("module m; typedef interface class my_ifc; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->name, "my_ifc");
}

TEST(TypeDeclParsing, ForwardTypedefEnum) {
  auto r = Parse("module m; typedef enum color_e; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "color_e");
}

TEST(TypeDeclParsing, ForwardTypedefStruct) {
  auto r = Parse("module m; typedef struct my_struct; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "my_struct");
}

TEST(TypeDeclParsing, ForwardTypedefUnion) {
  auto r = Parse("module m; typedef union my_union; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "my_union");
}

TEST(BlockItemDeclParsing, TypedefInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    typedef int my_int_t;\n"
              "    my_int_t x = 5;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(TypeDeclParsing, TypedefStruct) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kStruct);
}

TEST(TypeDeclParsing, TypedefUnionBody) {
  auto r = Parse(
      "module m;\n"
      "  typedef union { int i; logic [7:0] b; } val_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "val_t");
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
}

TEST(TypeDeclParsing, TypedefWithDims) {
  auto r = Parse("module m; typedef int arr_t [4]; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(BlockItemDeclParsing, TypedefInFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void foo();\n"
              "    typedef logic [7:0] byte_t;\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, TypeCompatibilityTypedefParsing) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit node;\n"
      "  typedef int type1;\n"
      "  typedef type1 type2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 3u);
}

TEST(DesignBuildingBlockParsing, TypedefInPackageScope) {
  auto r = Parse(
      "package types_pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef logic [15:0] word_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  auto* pkg = r.cu->packages[0];
  int typedef_count = 0;
  for (auto* item : pkg->items) {
    if (item->kind == ModuleItemKind::kTypedef) typedef_count++;
  }
  EXPECT_EQ(typedef_count, 2);
}

TEST(DataTypeParsing, TypedefInt) {
  auto r = Parse(
      "module t;\n"
      "  typedef int myint;\n"
      "  myint x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->data_type.type_name, "myint");
}

TEST(DataTypeParsing, BareForwardTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef my_type;\n"
      "  typedef int my_type;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DataTypeParsing, ForwardTypedefThenDefinition) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum color_e;\n"
      "  typedef enum {RED, GREEN, BLUE} color_e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DataTypeParsing, MultipleForwardTypedefs) {
  auto r = Parse(
      "module m;\n"
      "  typedef class myclass;\n"
      "  typedef class myclass;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DataTypeParsing, ForwardTypedefAfterDefinition) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {X, Y} my_enum;\n"
      "  typedef enum my_enum;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DataTypeParsing, TypedefForCastingUse) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  int x;\n"
      "  initial x = byte_t'(255);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DataTypeParsing, TypedefEnum) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {A, B, C} my_enum;\n"
      "  my_enum val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* td = r.cu->modules[0]->items[0];
  EXPECT_EQ(td->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(td->typedef_type.kind, DataTypeKind::kEnum);
  auto* var = r.cu->modules[0]->items[1];
  EXPECT_EQ(var->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(var->data_type.type_name, "my_enum");
}

TEST(DataTypeParsing, HierarchicalTypeReferenceRejected) {
  auto r = Parse(
      "module inner;\n"
      "  typedef int data_t;\n"
      "endmodule\n"
      "module outer;\n"
      "  inner i();\n"
      "  i.data_t x;\n"
      "endmodule\n");
  // `i` names no type, so the parse falls through to Parser::ParsePlainVarDecl
  // and the '.' is met where the §6.8 data declaration wants its ';'. §6.18 has
  // no report of its own here.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got '.'", 6, "6.8"));
}

TEST(DataTypeParsing, InterfacePortTypedef) {
  auto r = Parse(
      "interface intf_i;\n"
      "  typedef int data_t;\n"
      "endinterface\n"
      "module sub(intf_i p);\n"
      "  typedef p.data_t my_data_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ModuleItem* td = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kTypedef && item->name == "my_data_t") {
      td = item;
      break;
    }
  }
  ASSERT_NE(td, nullptr);
  EXPECT_EQ(td->typedef_ifc_port, "p");
  EXPECT_EQ(td->typedef_type.type_name, "data_t");
}

// §6.18 rules that "The declaration of a user-defined data type shall precede
// any reference to its type_identifier". `my_type x;` written above the typedef
// breaches it, and the breach is not the parser's to report: the same two
// identifiers and semicolon are what a module instantiation missing its port
// connection list spells, this parser holds no table of module names, and a
// module may be instantiated above its own declaration. What the parser records
// is the data declaration the shape also spells, with the type name kept, so
// that the elaborator has the name to report about.
// UserDefinedTypeElaboration.TypeReferenceBeforeItsDeclarationIsReported in
// test/src/unit/test_elaborator_subclause_06_18.cpp is where the §6.18 report
// is asserted.
TEST(DataTypeParsing, TypeReferenceBeforeDeclarationParsesAsADataDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  my_type x;\n"
      "  typedef int my_type;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->data_type.type_name, "my_type");
  EXPECT_TRUE(item->type_name_undeclared_at_parse);
}

// The six cases below cover the rest of A.2.4's variable_decl_assignment after
// a type name the parser has not yet met. The case above covers the sole
// declarator with no dimension and no initializer, which was for a time the
// only shape read as a declaration; A.2.3 gives
// `list_of_variable_decl_assignments ::= variable_decl_assignment { ,
// variable_decl_assignment }`, so the comma list, the initializer and the
// dimensions are the same data_declaration. None of them can be an
// instantiation: A.4.1.1 gives
// `hierarchical_instance ::= name_of_instance ( [ list_of_port_connections ] )`
// and §23.3.2 states it in prose -- "The parentheses shall be required on all
// module instantiations, even when the instantiated module does not have
// ports." -- and not one of the four sources contains a `(`.
//
// Each case asserts the node the parser built and not merely that nothing was
// reported, because the behaviour these replace reported an error and built a
// kModuleInst, so an assertion on the report alone would pass on a repair that
// silenced the report and left the wrong node.
TEST(ParserUndeclaredTypeDecl, ACommaSeparatedListIsADataDeclaration) {
  // §6.18 prints `intP a, b;` as its own example of using a named type, so this
  // is the shape the clause itself writes.
  auto r = Parse(
      "module m;\n"
      "  my_type a, b;\n"
      "  typedef int my_type;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2U);
  auto* first = r.cu->modules[0]->items[0];
  auto* second = r.cu->modules[0]->items[1];
  EXPECT_EQ(first->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(first->name, "a");
  EXPECT_EQ(second->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(second->name, "b");
  EXPECT_EQ(second->data_type.type_name, "my_type");
  EXPECT_TRUE(second->type_name_undeclared_at_parse);
}

TEST(ParserUndeclaredTypeDecl, AnInitializerIsADataDeclaration) {
  // `[ = expression ]` of A.2.4. The `=` used to reach ParsePortConnection,
  // where ParseExpr reported "expected expression" under §11.2 and consumed it.
  auto r = Parse(
      "module m;\n"
      "  my_type a = 0;\n"
      "  typedef int my_type;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "a");
  EXPECT_EQ(item->data_type.type_name, "my_type");
  EXPECT_NE(item->init_expr, nullptr);
  EXPECT_TRUE(item->type_name_undeclared_at_parse);
}

TEST(ParserUndeclaredTypeDecl, AnUnpackedDimensionIsADataDeclaration) {
  // `{ variable_dimension }` of A.2.4. This is the case that used to build a
  // kModuleInst carrying [3:0] as an instance range, so the assertion on the
  // dimension is what tells the two readings apart.
  auto r = Parse(
      "module m;\n"
      "  my_type a [3:0];\n"
      "  typedef int my_type;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "a");
  EXPECT_EQ(item->unpacked_dims.size(), 1U);
  EXPECT_TRUE(item->type_name_undeclared_at_parse);
}

TEST(ParserUndeclaredTypeDecl, AnUnsizedDimensionIsADataDeclaration) {
  // A.2.5's `unsized_dimension ::= [ ]`, which A.2.4 admits on the
  // dynamic_array_variable_identifier alternative. Parser::ParseUnpackedDims
  // records it as a null dimension, so the size alone would not distinguish it
  // from the sized case above.
  auto r = Parse(
      "module m;\n"
      "  my_type a [];\n"
      "  typedef int my_type;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  ASSERT_EQ(item->unpacked_dims.size(), 1U);
  EXPECT_EQ(item->unpacked_dims[0], nullptr);
}

// The two cases below hold the boundary from the instantiation side. Without
// them a repair reading every undeclared name as a type would pass all four
// cases above and stop the parser recognising an instantiation at all.
TEST(ParserUndeclaredTypeDecl, ANamedInstanceWithPortsIsStillAnInstantiation) {
  // The port-connection list A.4.1.1 requires, and §23.3.2 permits the module
  // to be "one declared later", so the parser cannot settle this by looking for
  // a declaration.
  auto r = Parse(
      "module m;\n"
      "  my_mod u (x, y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_mod");
  EXPECT_EQ(item->inst_name, "u");
}

TEST(ParserUndeclaredTypeDecl,
     AnInstanceWithARangeAndPortsIsStillAnInstantiation) {
  // A.4.1.1 puts `{ unpacked_dimension }` in name_of_instance, so an array of
  // instances wears the same brackets as a declarator's dimension and is told
  // from it only by the `(` that follows. This is the case that decides the
  // dimensions must be skipped before the `(` is looked for.
  auto r = Parse(
      "module m;\n"
      "  my_mod u [3:0] (x, y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_name, "u");
  EXPECT_NE(item->inst_range_left, nullptr);
}

}  // namespace
