#include "fixture_parser.h"

using namespace delta;

namespace {

// --- data_declaration: [const] [var] [lifetime] data_type_or_implicit
//     list_of_variable_decl_assignments ; ---

TEST(TypeDeclParsing, DataDeclTypeDeclaration) {
  auto r = Parse("module m; typedef int my_int_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
}

TEST(TypeDeclParsing, DataDeclBasicVariable) {
  auto r = Parse("module m; logic [7:0] data; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "data");
}

TEST(TypeDeclParsing, DataDeclConstPrefix) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    const int MAX = 100;\n"
      "  end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeDeclParsing, DataDeclVarPrefix) {
  auto r = Parse("module m; var logic x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
}

TEST(TypeDeclParsing, DataDeclMultipleAssignments) {
  auto r = Parse("module m; logic a, b, c; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) count++;
  }
  EXPECT_GE(count, 3);
}

// --- package_import_declaration ---

TEST(TypeDeclParsing, PackageImportWildcard) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::*; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->import_item.is_wildcard);
}

TEST(TypeDeclParsing, PackageImportItemNamed) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::my_func; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->import_item.package_name, "pkg");
  EXPECT_EQ(item->import_item.item_name, "my_func");
  EXPECT_FALSE(item->import_item.is_wildcard);
}

TEST(TypeDeclParsing, PackageImportMultipleItems) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::foo, pkg::bar; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- genvar_declaration ---

TEST(TypeDeclParsing, GenvarDeclSingle) {
  auto r = Parse("module m; genvar i; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "i");
}

TEST(TypeDeclParsing, GenvarDeclMultiple) {
  auto r = Parse("module m; genvar i, j, k; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "i");
  EXPECT_EQ(r.cu->modules[0]->items[1]->name, "j");
  EXPECT_EQ(r.cu->modules[0]->items[2]->name, "k");
}

// --- net_declaration ---

TEST(TypeDeclParsing, NetDeclWire) {
  auto r = Parse("module m; wire w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
}

TEST(TypeDeclParsing, NetDeclWirePackedDims) {
  auto r = Parse("module m; wire [7:0] bus; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

TEST(TypeDeclParsing, NetDeclTri) {
  auto r = Parse("module m; tri t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

TEST(TypeDeclParsing, NetDeclWandWor) {
  auto r = Parse("module m; wand wa; wor wo; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kNetDecl);
}

TEST(TypeDeclParsing, NetDeclWithInitializer) {
  auto r = Parse("module m; wire w = 1'b1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(TypeDeclParsing, NetDeclMultiple) {
  auto r = Parse("module m; wire a, b, c; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_GE(count, 3);
}

// --- type_declaration (typedef) ---

TEST(TypeDeclParsing, TypedefDataType) {
  auto r = Parse("module m; typedef logic [7:0] byte_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "byte_t");
}

TEST(TypeDeclParsing, TypedefEnumType) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "color_t");
}

TEST(TypeDeclParsing, TypedefStructType) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "pair_t");
}

// --- forward_type ---

TEST(TypeDeclParsing, ForwardTypedefEnum) {
  auto r = Parse("module m; typedef enum color_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "color_t");
}

TEST(TypeDeclParsing, ForwardTypedefStruct) {
  auto r = Parse("module m; typedef struct my_struct_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
}

TEST(TypeDeclParsing, ForwardTypedefUnion) {
  auto r = Parse("module m; typedef union my_union_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
}

TEST(TypeDeclParsing, ForwardTypedefClass) {
  auto r = Parse("module m; typedef class my_class_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
}

TEST(TypeDeclParsing, ForwardTypedefInterfaceClass) {
  auto r = Parse("module m; typedef interface class my_ifc_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
}

TEST(TypeDeclParsing, TypedefInterfacePortBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  typedef port0[0].my_type local_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->typedef_ifc_port, "port0");
  EXPECT_EQ(item->typedef_type.type_name, "my_type");
  EXPECT_EQ(item->name, "local_t");
  EXPECT_EQ(item->unpacked_dims.size(), 1u);
}

TEST(TypeDeclParsing, TypedefInterfacePortNoBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  typedef port0.my_type local_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->typedef_ifc_port, "port0");
  EXPECT_EQ(item->typedef_type.type_name, "my_type");
  EXPECT_EQ(item->name, "local_t");
  EXPECT_TRUE(item->unpacked_dims.empty());
}

// --- Error conditions ---

TEST(TypeDeclParsing, ErrorTypedefMissingSemicolon) {
  auto r = Parse("module m; typedef int my_t endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(TypeDeclParsing, ErrorImportMissingSemicolon) {
  auto r = Parse("module m; import pkg::foo endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(TypeDeclParsing, ErrorGenvarMissingSemicolon) {
  auto r = Parse("module m; genvar i endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(TypeDeclParsing, ErrorNetDeclMissingSemicolon) {
  auto r = Parse("module m; wire w endmodule");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
