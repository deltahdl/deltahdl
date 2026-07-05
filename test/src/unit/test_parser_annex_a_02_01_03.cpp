#include "fixture_parser.h"

using namespace delta;

namespace {

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

TEST(TypeDeclParsing, DataDeclConstVarPrefix) {
  // data_declaration admits [const] and [var] together; the type that follows
  // `var` is threaded through the const-var branch and the const flag survives.
  auto r = Parse("module m; const var logic x = 1'b1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  EXPECT_TRUE(item->data_type.is_const);
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

TEST(TypeDeclParsing, NetDeclWithDriveStrength) {
  auto r = Parse("module m; wire (strong0, weak1) w = 1'b1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

TEST(TypeDeclParsing, NetDeclTriregWithChargeStrength) {
  auto r = Parse("module m; trireg (small) cap; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

TEST(TypeDeclParsing, NetDeclVectored) {
  auto r = Parse("module m; wire vectored [7:0] bus; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

TEST(TypeDeclParsing, NetDeclScalared) {
  auto r = Parse("module m; wire scalared [7:0] bus; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

TEST(TypeDeclParsing, NetDeclWithDelay3) {
  auto r = Parse("module m; wire #(1, 2, 3) w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

TEST(TypeDeclParsing, NetDeclWireWithExplicitDataType) {
  auto r = Parse("module m; wire logic [7:0] bus; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

TEST(TypeDeclParsing, NetDeclInterconnectWithDelay) {
  auto r = Parse("module m; interconnect #5 x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_interconnect);
}

TEST(TypeDeclParsing, NetDeclInterconnectMultipleNetIdentifiers) {
  auto r = Parse("module m; interconnect a, b, c; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int net_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl &&
        item->data_type.is_interconnect)
      ++net_count;
  }
  EXPECT_GE(net_count, 3);
}

TEST(TypeDeclParsing, TypedefWithVariableDimension) {
  auto r = Parse("module m; typedef int arr_t [10]; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "arr_t");
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

TEST(TypeDeclParsing, NettypeDeclAliasForm) {
  auto r = Parse(
      "module m;\n"
      "  nettype real base_nt;\n"
      "  nettype base_nt alias_nt;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int nettype_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNettypeDecl) ++nettype_count;
  }
  EXPECT_EQ(nettype_count, 2);
}

TEST(TypeDeclParsing, DataDeclStaticLifetime) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    static int counter = 0;\n"
      "  endfunction\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeDeclParsing, DataDeclAutomaticLifetime) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    automatic int tmp = 0;\n"
      "  endfunction\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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

TEST(TypeDeclParsing, DataDeclNettypeDeclaration) {
  auto r = Parse("module m; nettype real real_net; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->name, "real_net");
}

TEST(TypeDeclParsing, NettypeDeclWithResolutionFunction) {
  auto r = Parse(
      "package p;\n"
      "  function automatic real sum(real a, real b); return a + b; "
      "endfunction\n"
      "  nettype real resolved_net with p::sum;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeDeclParsing, PackageExportStarStar) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "package q;\n"
      "  import pkg::*;\n"
      "  export *::*;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeDeclParsing, PackageExportItemNamed) {
  auto r = Parse(
      "package pkg; function automatic int f(); return 0; endfunction "
      "endpackage\n"
      "package q;\n"
      "  import pkg::f;\n"
      "  export pkg::f;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeDeclParsing, PackageExportWildcardFromPackage) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "package q;\n"
      "  import pkg::*;\n"
      "  export pkg::*;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeDeclParsing, PackageExportMultipleItems) {
  auto r = Parse(
      "package p;\n"
      "  export p1::a, p2::b;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* pkg = r.cu->packages[0];
  int export_count = 0;
  for (auto* item : pkg->items) {
    if (item->kind == ModuleItemKind::kExportDecl) ++export_count;
  }
  EXPECT_EQ(export_count, 2);
}

TEST(TypeDeclParsing, NetDeclWithNettypeIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  nettype real my_real;\n"
      "  my_real x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeDeclParsing, NetDeclInterconnect) {
  auto r = Parse("module m; interconnect w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->data_type.is_interconnect);
  EXPECT_EQ(item->name, "w");
}

TEST(TypeDeclParsing, NetDeclInterconnectWithPackedDim) {
  auto r = Parse("module m; interconnect [3:0] bus; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->data_type.is_interconnect);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

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

TEST(TypeDeclParsing, ErrorExportMissingSemicolon) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "package q; export pkg::* endpackage");
  EXPECT_TRUE(r.has_errors);
}

TEST(TypeDeclParsing, ErrorNettypeMissingSemicolon) {
  auto r = Parse("module m; nettype real foo endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(TypeDeclParsing, ErrorNettypeWithoutDataType) {
  // nettype_declaration alt-1 makes the data_type mandatory; a lone
  // `nettype name;` with no data type must be rejected.
  auto r = Parse("module m; nettype foo; endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(TypeDeclParsing, ErrorAutomaticAtModuleScope) {
  auto r = Parse("module m; automatic int x; endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(TypeDeclParsing, ErrorImplicitDataTypeWithLifetimeAtModuleScope) {
  auto r = Parse("module m; static x = 1; endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(TypeDeclParsing, ErrorImplicitDataTypeWithoutVarInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static x = 1;\n"
      "  end\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(TypeDeclParsing, ErrorImportInsideClassScope) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "class c;\n"
      "  import pkg::*;\n"
      "endclass");
  EXPECT_TRUE(r.has_errors);
}

TEST(TypeDeclParsing, ErrorChargeStrengthOnNonTriregNet) {
  auto r = Parse("module m; wire (small) bus; endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(TypeDeclParsing, NetDeclNettypeIdentifierWithDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  nettype real my_real;\n"
      "  my_real #5 x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TypeDeclParsing, NetDeclInterconnectWithUnpackedDim) {
  auto r = Parse("module m; interconnect bus[10]; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_interconnect);
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

TEST(TypeDeclParsing, ForwardTypedefWithoutKeyword) {
  auto r = Parse("module m; typedef incomplete_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "incomplete_t");
}

}  // namespace
