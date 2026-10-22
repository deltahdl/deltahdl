#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

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

// A.2.1.3 gives an interconnect declaration a second net after a comma.
TEST(TypeDeclParsing, NetDeclInterconnectMultipleNetIdentifiers) {
  auto r = Parse("module m; interconnect a, b; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int net_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl &&
        item->data_type.is_interconnect)
      ++net_count;
  }
  EXPECT_EQ(net_count, 2);
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

// The five ForwardType* cases below cover the alternatives of the
// forward_type nonterminal in the A.2.1.3 type_declaration production
// (forward_type ::= enum | struct | union | class | interface class).
// test_parser_subclause_06_18.cpp carries the matching prose cases for the
// forward typedef forms listed in 6.18.
TEST(TypeDeclParsing, ForwardTypeEnum) {
  auto r = Parse("module m; typedef enum color_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "color_t");
}

TEST(TypeDeclParsing, ForwardTypeStruct) {
  auto r = Parse("module m; typedef struct my_struct_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
}

TEST(TypeDeclParsing, ForwardTypeUnion) {
  auto r = Parse("module m; typedef union my_union_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
}

TEST(TypeDeclParsing, ForwardTypeClass) {
  auto r = Parse("module m; typedef class my_class_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
}

TEST(TypeDeclParsing, ForwardTypeInterfaceClass) {
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
  // §6.18 owns type_declaration, so its terminator is demanded there.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 1, "6.18"));
}

TEST(TypeDeclParsing, ErrorImportMissingSemicolon) {
  auto r = Parse("module m; import pkg::foo endmodule");
  // §26.3 owns package_import_declaration, so its terminator is demanded
  // there.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 1, "26.3"));
}

TEST(TypeDeclParsing, ErrorGenvarMissingSemicolon) {
  auto r = Parse("module m; genvar i endmodule");
  // §27.4 owns genvar_declaration, so its terminator is demanded there.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 1, "27.4"));
}

TEST(TypeDeclParsing, ErrorNetDeclMissingSemicolon) {
  auto r = Parse("module m; wire w endmodule");
  // §6.7 states the net declaration, so the declarator list a net type heads
  // takes its terminator's report from there.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 1, "6.7"));
}

TEST(TypeDeclParsing, ErrorExportMissingSemicolon) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "package q; export pkg::* endpackage");
  // §26.6 owns package_export_declaration, so its terminator is demanded
  // there.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endpackage'", 2, "26.6"));
}

TEST(TypeDeclParsing, ErrorNettypeMissingSemicolon) {
  auto r = Parse("module m; nettype real foo endmodule");
  // §6.6.7 owns nettype_declaration, so its terminator is demanded there.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 1, "6.6.7"));
}

TEST(TypeDeclParsing, ErrorNettypeWithoutDataType) {
  // nettype_declaration alt-1 makes the data_type mandatory; a lone
  // `nettype name;` with no data type must be rejected.
  auto r = Parse("module m; nettype foo; endmodule");
  EXPECT_TRUE(ReportedError(
      r.diags, "nettype declaration requires an explicit data type", 1,
      "6.6.7"));
}

TEST(TypeDeclParsing, ErrorAutomaticAtModuleScope) {
  auto r = Parse("module m; automatic int x; endmodule");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'automatic' is not allowed in a data_declaration "
                            "outside a procedural context",
                            1, "6.8"));
}

TEST(TypeDeclParsing, ErrorImplicitDataTypeWithLifetimeAtModuleScope) {
  auto r = Parse("module m; static x = 1; endmodule");
  EXPECT_TRUE(ReportedError(r.diags,
                            "data_declaration without an explicit data type "
                            "requires the 'var' keyword",
                            1, "6.8"));
}

TEST(TypeDeclParsing, ErrorImplicitDataTypeWithoutVarInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static x = 1;\n"
      "  end\n"
      "endmodule");
  EXPECT_TRUE(ReportedError(r.diags,
                            "data_declaration without an explicit data type "
                            "requires the 'var' keyword",
                            3, "6.8"));
}

TEST(TypeDeclParsing, ErrorImportInsideClassScope) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "class c;\n"
      "  import pkg::*;\n"
      "endclass");
  EXPECT_TRUE(ReportedError(
      r.diags, "package import declaration is not allowed in class scope", 3,
      "26.3"));
}

TEST(TypeDeclParsing, ErrorChargeStrengthOnNonTriregNet) {
  auto r = Parse("module m; wire (small) bus; endmodule");
  // §6.3.2.1 states the charge strength rule, so the report is filed there.
  EXPECT_TRUE(ReportedError(r.diags,
                            "charge strength can only be used with trireg nets",
                            1, "6.3.2.1"));
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

// A.2.1.3 opens a data_declaration with `const`, then `var`, then a lifetime,
// each optional, and §6.8's Syntax 6-3 repeats the order. Outside a class,
// whose class_property puts qualifiers of its own in front, a qualifier
// written after one that follows it in that order, or written twice, is
// reported where it stands (#7589).
TEST(TypeDeclParsing, DataDeclQualifiersOutOfOrderAreErrors) {
  auto r = Parse(
      "module m;\n"
      "  static var logic a;\n"
      "  var const int b = 1;\n"
      "  initial begin\n"
      "    automatic var c = 1'b0;\n"
      "    static const int d = 2;\n"
      "    var var int e;\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line : {2U, 3U, 5U, 6U, 7U}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a data declaration writes 'const', then 'var', "
                              "then its lifetime, each at most once",
                              line, "A.2.1.3"));
  }
}

// Written in A.2.1.3's order, the qualifiers parse at module level and in a
// block alike, a lifetime after `const` or `var` included, and a class
// property keeps its leading `static` (#7589).
TEST(TypeDeclParsing, DataDeclQualifiersInOrderParse) {
  auto r = Parse(
      "module m;\n"
      "  var static logic a;\n"
      "  const var int b = 1;\n"
      "  const static int c = 2;\n"
      "  const var static int d = 3;\n"
      "  initial begin\n"
      "    var automatic e = 1'b0;\n"
      "    const static int f = 2;\n"
      "  end\n"
      "endmodule\n"
      "class k;\n"
      "  static const int w = 3;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// A.2.1.3 and §6.7's Syntax 6-2 give an interconnect declaration one net and
// at most one more, so each net after the second is reported where it stands,
// and the declaration is still read (#7590).
TEST(TypeDeclParsing, InterconnectDeclThirdNetIsError) {
  auto r = Parse(
      "module m;\n"
      "  interconnect a, b,\n"
      "    c, d;\n"
      "  interconnect e, f;\n"
      "endmodule\n");
  const char* const kTwoNets =
      "an interconnect declaration names one net, or two";
  EXPECT_TRUE(ReportedError(r.diags, kTwoNets, 3, "A.2.1.3"));
  EXPECT_FALSE(ReportedError(r.diags, kTwoNets, 2, "A.2.1.3"));
  EXPECT_FALSE(ReportedError(r.diags, kTwoNets, 4, "A.2.1.3"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->items.size(), 6u);
}

// A.2.1.3 writes a nettype's resolution function after an optional
// package_scope or class_scope, and A.2.2.1 makes a class_scope a class_type:
// a class name with an optional parameter_value_assignment, itself named
// through a package or $unit, followed by the names of the classes nested in
// it. The scope is kept as the class_type or package it names, its last name
// the one declaring the function, and a specialization's parameter values are
// kept with it (#7592).
TEST(TypeDeclParsing, NettypeWithClauseReadsAClassScopeChain) {
  auto r = Parse(
      "module m;\n"
      "  nettype real n1 with P::C#(8)::resolve;\n"
      "  nettype real n2 with Outer::Inner::resolve;\n"
      "  nettype real n3 with P::Outer::Inner::resolve;\n"
      "  nettype real n4 with $unit::C#(4, 5)::resolve;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 4u);
  for (const ModuleItem* item : items) {
    EXPECT_EQ(item->nettype_resolve_func, "resolve");
    ASSERT_NE(item->nettype_resolve_scope, nullptr);
  }
  const DataType& n1 = *items[0]->nettype_resolve_scope;
  EXPECT_TRUE(n1.outer_scope_names.empty());
  EXPECT_EQ(n1.scope_name, "P");
  EXPECT_EQ(n1.type_name, "C");
  EXPECT_EQ(n1.type_params.size(), 1u);
  const DataType& n2 = *items[1]->nettype_resolve_scope;
  EXPECT_EQ(n2.scope_name, "Outer");
  EXPECT_EQ(n2.type_name, "Inner");
  EXPECT_TRUE(n2.type_params.empty());
  const DataType& n3 = *items[2]->nettype_resolve_scope;
  ASSERT_EQ(n3.outer_scope_names.size(), 1u);
  EXPECT_EQ(n3.outer_scope_names[0], "P");
  EXPECT_EQ(n3.scope_name, "Outer");
  EXPECT_EQ(n3.type_name, "Inner");
  const DataType& n4 = *items[3]->nettype_resolve_scope;
  EXPECT_EQ(n4.scope_name, "$unit");
  EXPECT_EQ(n4.type_name, "C");
  EXPECT_EQ(n4.type_params.size(), 2u);
}

// A.2.2.1's package_scope is a package name or `$unit`, each followed by `::`,
// so `with $unit::f` names the compilation unit's function f, and a with clause
// writing no scope keeps none.
TEST(TypeDeclParsing, NettypeWithClauseReadsAUnitOrPackageScope) {
  auto r = Parse(
      "module m;\n"
      "  nettype real n1 with $unit::ufn;\n"
      "  nettype real n2 with P::pfn;\n"
      "  nettype real n3 with fn;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  ASSERT_NE(items[0]->nettype_resolve_scope, nullptr);
  EXPECT_EQ(items[0]->nettype_resolve_scope->type_name, "$unit");
  EXPECT_TRUE(items[0]->nettype_resolve_scope->scope_name.empty());
  EXPECT_EQ(items[0]->nettype_resolve_func, "ufn");
  ASSERT_NE(items[1]->nettype_resolve_scope, nullptr);
  EXPECT_EQ(items[1]->nettype_resolve_scope->type_name, "P");
  EXPECT_EQ(items[1]->nettype_resolve_func, "pfn");
  EXPECT_EQ(items[2]->nettype_resolve_scope, nullptr);
  EXPECT_EQ(items[2]->nettype_resolve_func, "fn");
}

// `$unit` opens a package_scope and is never the function itself, so a with
// clause ending at `$unit`, or at `$unit::`, is missing the function's name,
// as one naming nothing at all is.
TEST(TypeDeclParsing, NettypeWithClauseOfUnitAloneIsError) {
  auto r = Parse(
      "module m;\n"
      "  nettype real n1 with $unit;\n"
      "  nettype real n2 with $unit::;\n"
      "  nettype real n3 with ;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '::', got ';'", 2, "A.2.1.3"));
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 3, "A.2.1.3"));
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 4, "6.6.7"));
}

// A.2.2.1 lets a data_type open with a package_scope, and A.2.1.3's second
// nettype form names its source nettype through one, so a nettype may take a
// type a package declares and may rename a package's nettype. Neither package
// name is a type the parser knows, and each declaration is still read whole,
// its scope kept (#7593).
TEST(TypeDeclParsing, NettypeOfAPackageScopedTypeOrNettype) {
  auto r = Parse(
      "package P;\n"
      "  typedef struct { real r; } T;\n"
      "  nettype real nt;\n"
      "endpackage\n"
      "module m;\n"
      "  nettype P::T tnet;\n"
      "  nettype P::nt alias_nt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->name, "tnet");
  EXPECT_EQ(items[0]->typedef_type.scope_name, "P");
  EXPECT_EQ(items[0]->typedef_type.type_name, "T");
  EXPECT_EQ(items[1]->name, "alias_nt");
  EXPECT_EQ(items[1]->typedef_type.scope_name, "P");
  EXPECT_EQ(items[1]->typedef_type.type_name, "nt");
}

// A.2.1.3 lets const, var and a lifetime open a data_declaration, and A.2.2.1
// lets its data type be named through a package scope, which no qualifier
// rules out. Outside procedural code every qualified form was read as an
// implicit type: P taken for the variable's name after `var`, and the
// declaration reported as wanting `var` after `const` or `static` (#7603).
TEST(TypeDeclParsing, AQualifiedDataDeclarationTakesAPackageScopedType) {
  auto r = Parse(
      "package P;\n"
      "  typedef logic [3:0] T;\n"
      "endpackage\n"
      "module m;\n"
      "  var P::T a;\n"
      "  const P::T b = 4'hA;\n"
      "  static P::T c;\n"
      "  const var static P::T d = 4'h5;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 4u);
  const char* const kNames[] = {"a", "b", "c", "d"};
  for (std::size_t i = 0; i < items.size(); ++i) {
    EXPECT_EQ(items[i]->kind, ModuleItemKind::kVarDecl) << i;
    EXPECT_EQ(items[i]->name, kNames[i]);
    EXPECT_EQ(items[i]->data_type.scope_name, "P") << i;
    EXPECT_EQ(items[i]->data_type.type_name, "T") << i;
  }
  EXPECT_FALSE(items[0]->data_type.is_const);
  EXPECT_TRUE(items[1]->data_type.is_const);
  EXPECT_FALSE(items[2]->data_type.is_const);
  EXPECT_TRUE(items[3]->data_type.is_const);
}

// §6.8 reports `automatic` on a data declaration outside procedural code, and
// the declaration it opens still takes its package-scoped type, so the report
// that an implicit type wants `var` is not filed beside it.
TEST(TypeDeclParsing, AnAutomaticPackageScopedDeclarationReportsTheLifetime) {
  auto r = Parse(
      "package P;\n"
      "  typedef logic [3:0] T;\n"
      "endpackage\n"
      "module m;\n"
      "  automatic P::T e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "'automatic' is not allowed in a data_declaration "
                            "outside a procedural context",
                            5, "6.8"));
  EXPECT_FALSE(ReportedError(r.diags,
                             "data_declaration without an explicit data type "
                             "requires the 'var' keyword",
                             5, "6.8"));
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->name, "e");
  EXPECT_EQ(items[0]->data_type.scope_name, "P");
}

}  // namespace
