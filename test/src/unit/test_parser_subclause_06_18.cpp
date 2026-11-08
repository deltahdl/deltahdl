#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

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

TEST(ParserUndeclaredTypeDecl, ACommaSeparatedListIsADataDeclaration) {
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

TEST(ParserUndeclaredTypeDecl, ANamedInstanceWithPortsIsStillAnInstantiation) {
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

static void ExpectQualifiedTypedef(const char* qualified, const char* scope,
                                   const char* type_name) {
  std::string src = std::string("module m;\n  typedef ") + qualified +
                    " alias_t;\nendmodule\n";
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  const auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "alias_t");
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->typedef_type.scope_name, scope);
  EXPECT_EQ(item->typedef_type.type_name, type_name);
  EXPECT_EQ(item->forward_type_kind, DataTypeKind::kImplicit);
}

TEST(TypeDeclParsing, PackageQualifiedTypedefType) {
  ExpectQualifiedTypedef("r::real_holder_t", "r", "real_holder_t");
}

TEST(TypeDeclParsing, ClassQualifiedTypedefType) {
  ExpectQualifiedTypedef("C::T", "C", "T");
}

TEST(TypeDeclParsing, ForwardStructTypedefStaysForward) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct pair_t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 2u);
  const auto* fwd = r.cu->modules[0]->items[0];
  EXPECT_EQ(fwd->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(fwd->name, "pair_t");
  EXPECT_EQ(fwd->forward_type_kind, DataTypeKind::kStruct);
  EXPECT_EQ(fwd->typedef_type.kind, DataTypeKind::kImplicit);
}

TEST(TypeDeclParsing, TypedefOfAnInlineAggregateTakesPackedDimensions) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { int i1; bit bvec; } [1:3] parrtype;\n"
      "  typedef union packed { bit [3:0] x; logic [3:0] y; } [5:0][1:0] u_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 2u);
  const auto* parr = r.cu->modules[0]->items[0];
  EXPECT_EQ(parr->name, "parrtype");
  EXPECT_EQ(parr->typedef_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(parr->typedef_type.is_packed);
  EXPECT_EQ(parr->typedef_type.struct_members.size(), 2u);
  ASSERT_NE(parr->typedef_type.packed_dim_left, nullptr);
  EXPECT_EQ(parr->typedef_type.packed_dim_left->int_val, 1u);
  EXPECT_EQ(parr->typedef_type.packed_dim_right->int_val, 3u);
  const auto* u = r.cu->modules[0]->items[1];
  EXPECT_EQ(u->name, "u_t");
  EXPECT_EQ(u->typedef_type.kind, DataTypeKind::kUnion);
  ASSERT_NE(u->typedef_type.packed_dim_left, nullptr);
  EXPECT_EQ(u->typedef_type.packed_dim_left->int_val, 5u);
  EXPECT_EQ(u->typedef_type.extra_packed_dims.size(), 1u);
}

}  // namespace
