#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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
  EXPECT_TRUE(r.has_errors);
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

TEST(DataTypeParsing, TypeReferenceBeforeDeclarationRejected) {
  auto r = Parse(
      "module m;\n"
      "  my_type x;\n"
      "  typedef int my_type;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
