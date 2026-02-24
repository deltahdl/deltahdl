// Non-LRM tests

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// description: package_declaration
TEST(SourceText, DescriptionPackage) {
  auto r = Parse("package pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

// description: class_declaration
TEST(SourceText, DescriptionClass) {
  auto r = Parse("class C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

// Package with items and lifetime.
TEST(SourceText, PackageLifetimeWithItems) {
  auto r = Parse(
      "package automatic pkg;\n"
      "  parameter int W = 8;\n"
      "  typedef logic [W-1:0] word_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  EXPECT_EQ(r.cu->packages[0]->items.size(), 2u);
}

// Checker with end label.
TEST(SourceText, CheckerEndLabel) {
  auto r = Parse("checker chk; endchecker : chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// description: { attribute_instance } package_item (file-scope task)
TEST(SourceText, DescriptionPackageItemTask) {
  auto r = Parse("task my_task; endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
}

// Class with implements clause.
TEST(SourceText, ClassWithImplements) {
  auto r = Parse("class C implements I; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

// Interface with non-ANSI ports.
TEST(SourceText, InterfaceNonAnsiHeader) {
  auto r = Parse(
      "interface ifc(clk);\n"
      "  input clk;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
}

// specparam_declaration as non_port_module_item (outside specify block).
TEST(SourceText, SpecparamAsModuleItem) {
  auto r = Parse(
      "module m;\n"
      "  specparam delay = 10;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kSpecparam);
}

TEST(ParserAnnexA, A2VarDeclWithInit) {
  auto r = Parse("module m; logic [7:0] data = 8'hFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_NE(r.cu->modules[0]->items[0]->init_expr, nullptr);
}

TEST(ParserAnnexA, A2TypedefStructPacked) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] addr;\n"
      "    logic [31:0] data;\n"
      "  } req_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

TEST(ParserAnnexA, A2ClassWithConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c1 { x > 0; x < 100; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserAnnexA, A2CovergroupDecl) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA212, InoutUnpackedDim) {
  auto r = Parse("module m(inout logic a [3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ParserA212, InputUnpackedDim) {
  // list_of_variable_identifiers: variable_identifier { variable_dimension }
  auto r = Parse("module m(input logic d [3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ParserA212, OutputUnpackedDim) {
  auto r = Parse("module m(output logic q [1:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &port = r.cu->modules[0]->ports[0];
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ParserA212, RefUnpackedDim) {
  auto r = Parse("module m(ref int arr [4]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ParserA213, DataDeclMultipleAssign) {
  // list_of_variable_decl_assignments: multiple names
  auto r = Parse("module m; int a = 1, b = 2; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) count++;
  }
  EXPECT_GE(count, 2);
}

TEST(ParserA213, DataDeclPackageImport) {
  // package_import_declaration alternative
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::*; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- package_import_declaration ---
// import package_import_item { , package_import_item } ;
TEST(ParserA213, PackageImportSingle) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::foo; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "pkg");
  EXPECT_EQ(item->import_item.item_name, "foo");
}

TEST(ParserA213, PackageImportMultiple) {
  // Multiple comma-separated import items
  auto r = Parse(
      "package p1; endpackage\n"
      "package p2; endpackage\n"
      "module m; import p1::a, p2::b; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int import_count = 0;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kImportDecl) import_count++;
  }
  EXPECT_GE(import_count, 2);
}

TEST(ParserA213, PackageExportMultipleItems) {
  // BNF: export package_import_item { , package_import_item } ;
  auto r = Parse(
      "package pkg;\n"
      "  export p1::a, p2::b;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int export_count = 0;
  for (auto *item : r.cu->packages[0]->items) {
    if (item->kind == ModuleItemKind::kExportDecl) export_count++;
  }
  EXPECT_GE(export_count, 2);
}

TEST(ParserA213, TypedefWithDims) {
  auto r = Parse("module m; typedef int arr_t [4]; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(ParserA213, TypedefStruct) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kStruct);
}

// --- data_type --- (12 alternatives)
// integer_vector_type [signing] {packed_dimension}
TEST(ParserA221, DataTypeIntegerVector) {
  auto r = Parse("module m; logic signed [7:0] a; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

// struct_union [packed [signing]] { ... } {packed_dimension}
TEST(ParserA221, DataTypeStructPacked) {
  auto r = Parse(
      "module m;\n"
      "  struct packed signed { logic [7:0] a; logic [7:0] b; } pair;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_TRUE(item->data_type.is_signed);
}

// [class_scope | package_scope] type_identifier {packed_dimension}
TEST(ParserA221, DataTypeScopedType) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int my_int_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  pkg::my_int_t x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- data_type_or_implicit ---
// data_type | implicit_data_type
// --- implicit_data_type ---
// [signing] {packed_dimension}
TEST(ParserA221, ImplicitDataType) {
  // Implicit data type with just packed dimension
  auto r = Parse("module m(input [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &port = r.cu->modules[0]->ports[0];
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ParserA221, ImplicitDataTypeSigned) {
  // signed [7:0]
  auto r = Parse("module m(input signed [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.data_type.is_signed);
}

// --- enum_base_type ---
// integer_atom_type [signing] | integer_vector_type [signing] [packed_dim]
// | type_identifier [packed_dimension]
TEST(ParserA221, EnumBaseAtomType) {
  auto r = Parse("module m; enum int {A, B} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
}

// --- enum_name_declaration ---
// enum_id [ [ integral_number [ : integral_number ] ] ] [ = const_expr ]
TEST(ParserA221, EnumNameBasic) {
  auto r = Parse("module m; enum {RED, GREEN, BLUE} color; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.enum_members.size(), 3u);
}

TEST(ParserA221, EnumNameWithRangeColon) {
  // enum_id [ integral_number : integral_number ]
  auto r = Parse("module m; enum {A[0:3] = 10} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &member = r.cu->modules[0]->items[0]->data_type.enum_members[0];
  EXPECT_NE(member.range_start, nullptr);
  EXPECT_NE(member.range_end, nullptr);
  EXPECT_NE(member.value, nullptr);
}

// --- class_scope ---
// class_type ::
TEST(ParserA221, ClassScope) {
  auto r = Parse(
      "class base_cls;\n"
      "  typedef int inner_t;\n"
      "endclass\n"
      "module m; base_cls::inner_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- class_type ---
// ps_class_identifier [param] { :: class_identifier [param] }
TEST(ParserA221, ClassTypeParameterized) {
  auto r = Parse(
      "class param_cls #(type T = int);\n"
      "  typedef T value_t;\n"
      "endclass\n"
      "module m; param_cls#(int)::value_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- simple_type ---
// integer_type | non_integer_type | ps_type_identifier |
// ps_parameter_identifier (covered by casting_type and data_type tests above)
// --- struct_union ---
// struct | union [soft | tagged]
TEST(ParserA221, StructUnionStruct) {
  auto r = Parse(
      "module m;\n"
      "  struct { int a; int b; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kStruct);
}

TEST(ParserA221, StructUnionUnionTagged) {
  auto r = Parse(
      "module m;\n"
      "  union tagged { int a; real b; } u;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->data_type.is_tagged);
}

// --- struct_union_member ---
// {attribute_instance} [random_qualifier] data_type_or_void
//   list_of_variable_decl_assignments ;
TEST(ParserA221, StructMemberBasic) {
  auto r = Parse(
      "module m;\n"
      "  struct { logic [7:0] data; int count; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &members = r.cu->modules[0]->items[0]->data_type.struct_members;
  EXPECT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0].name, "data");
  EXPECT_EQ(members[1].name, "count");
}

TEST(ParserA221, StructMemberRand) {
  // random_qualifier: rand
  auto r = Parse(
      "module m;\n"
      "  struct { rand int a; int b; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 2u);
  EXPECT_TRUE(members[0].is_rand);
  EXPECT_FALSE(members[1].is_rand);
}

TEST(ParserA221, StructMemberRandc) {
  // random_qualifier: randc
  auto r = Parse(
      "module m;\n"
      "  struct { randc bit [7:0] x; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 1u);
  EXPECT_TRUE(members[0].is_randc);
}

TEST(ParserA221, StructMemberAttr) {
  // {attribute_instance} before struct member
  auto r = Parse(
      "module m;\n"
      "  struct { (* mark *) int a; int b; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &members = r.cu->modules[0]->items[0]->data_type.struct_members;
  ASSERT_GE(members.size(), 2u);
  EXPECT_FALSE(members[0].attrs.empty());
  EXPECT_TRUE(members[1].attrs.empty());
}

TEST(ParserA23, ListOfDefparamAssignmentsThree) {
  auto r = Parse(
      "module top;\n"
      "  defparam u0.A = 1, u0.B = 2, u0.C = 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->defparam_assigns.size(), 3u);
}

TEST(ParserA23, ListOfGenvarIdentifiersMultiple) {
  auto r = Parse("module m; genvar i, j, k; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "i");
  EXPECT_EQ(r.cu->modules[0]->items[1]->name, "j");
  EXPECT_EQ(r.cu->modules[0]->items[2]->name, "k");
}

TEST(ParserA23, ListOfInterfaceIdentifiersMultiple) {
  auto r = Parse("module m(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "b");
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "c");
}

TEST(ParserA23, ListOfParamAssignmentsWithDims) {
  auto r = Parse(
      "module m;\n"
      "  parameter int A [2] = '{1, 2}, B [3] = '{3, 4, 5};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) count++;
  }
  EXPECT_GE(count, 2);
}

// --- list_of_udp_port_identifiers ---
// port_identifier { , port_identifier }
TEST(ParserA23, ListOfUdpPortIdentifiersSingle) {
  auto r = Parse(
      "primitive buf_p(output out, input in);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA23, ListOfSpecparamAssignmentsMultiple) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 100, tFALL = 50, tHOLD = 10; endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- list_of_tf_variable_identifiers ---
// port_identifier { variable_dimension } [ = expression ]
//     { , port_identifier { variable_dimension } [ = expression ] }
TEST(ParserA23, ListOfTfVariableIdentifiersSingle) {
  auto r = Parse(
      "module m;\n"
      "  function int f;\n"
      "    input int a;\n"
      "    f = a;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->func_args.size(), 1u);
}

TEST(ParserA23, ListOfTfVariableIdentifiersMultiple) {
  auto r = Parse(
      "module m;\n"
      "  function int add;\n"
      "    input int a, b;\n"
      "    add = a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[1].name, "b");
}

TEST(ParserA23, ListOfTypeAssignmentsMultiple) {
  auto r = Parse(
      "module m; parameter type T1 = int, T2 = real, T3 = string; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) count++;
  }
  EXPECT_GE(count, 3);
}

TEST(ParserA23, ListOfVariableDeclAssignmentsWithDims) {
  auto r = Parse("module m; logic [7:0] mem [256], cache [64]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) count++;
  }
  EXPECT_GE(count, 2);
}

// --- net_decl_assignment ---
// net_identifier { unpacked_dimension } [ = expression ]
TEST(ParserA24, NetDeclAssignmentBasic) {
  auto r = Parse("module m; wire w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_EQ(item->init_expr, nullptr);  // No initializer
}

TEST(ParserA24, NetDeclAssignmentWithUnpackedDims) {
  auto r = Parse("module m; wire w [3:0][7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

TEST(ParserA24, NetDeclAssignmentDimsAndInit) {
  auto r = Parse("module m; wire [7:0] mem [0:3] = '{0,1,2,3}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->init_expr, nullptr);
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

// --- param_assignment ---
// parameter_identifier { variable_dimension } [ = constant_param_expression ]
TEST(ParserA24, ParamAssignmentBasic) {
  auto r = Parse("module m; parameter WIDTH = 8; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "WIDTH");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserA24, ParamAssignmentWithUnpackedDim) {
  auto r = Parse("module m; parameter int ARR [3:0] = '{1,2,3,4}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "ARR");
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

TEST(ParserA24, VarDeclAssignmentWithInit) {
  auto r = Parse("module m; int x = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  EXPECT_NE(item->init_expr, nullptr);
}

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

RtlirDesign *Elaborate(const std::string &src, ElabFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

TEST(ParserA25, UnsizedDimWithInitInferSize) {
  ElabFixture f;
  auto *design = Elaborate("module m; int d [] = '{1,2,3}; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_dynamic);
  EXPECT_EQ(mod->variables[0].unpacked_size, 3u);
}

// ---------------------------------------------------------------------------
// function_body_declaration (old-style ports)
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncBodyOldStylePorts) {
  auto r = Parse(
      "module m;\n"
      "  function int foo;\n"
      "    input int a;\n"
      "    input int b;\n"
      "    foo = a + b;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

TEST(ParserA26, FuncPrototypeExternVoid) {
  auto r = Parse(
      "module m;\n"
      "  extern function void bar();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_extern);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

TEST(ParserA27, TaskBodyNewStyleBlockItemDecl) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int x);\n"
      "    int temp;\n"
      "    temp = x + 1;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_GE(item->func_body_stmts.size(), 1u);
}

TEST(ParserA27, TaskBodyWithStatements) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int x);\n"
      "    #10;\n"
      "    $display(\"x=%0d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_GE(item->func_body_stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// tf_port_item: [ var ] data_type_or_implicit
// ---------------------------------------------------------------------------
TEST(ParserA27, TfPortItemVar) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(var int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(ParserA27, TfPortDeclOldStyleVar) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    input var int x;\n"
      "    $display(\"%0d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// §A.2.8 block_item_declaration alternative 1: data_declaration
// data_declaration ::= [ const ] [ var ] [ lifetime ] data_type_or_implicit
//                      list_of_variable_decl_assignments ;
TEST(ParserA28, DataDeclBasicInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "x");
}

TEST(ParserA28, DataDeclUnpackedDimsInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int arr[3];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_unpacked_dims.size(), 1u);
}

// attribute_instance prefix on block items
TEST(ParserA28, AttrOnDataDeclInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* synthesis *) int x;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA28, AttrOnLocalparamInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* synthesis *) localparam int X = 5;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA28, BlockItemInForkJoinAny) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    int x;\n"
              "    x = 1;\n"
              "  join_any\n"
              "endmodule\n"));
}

TEST(ParserA28, BlockItemInForkJoinNone) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    int x;\n"
              "    x = 1;\n"
              "  join_none\n"
              "endmodule\n"));
}

// let_declaration in function body
TEST(ParserA28, LetDeclInFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void foo();\n"
              "    let inc(x) = x + 1;\n"
              "  endfunction\n"
              "endmodule\n"));
}

// typedef in function body
TEST(ParserA28, TypedefInFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void foo();\n"
              "    typedef logic [7:0] byte_t;\n"
              "  endfunction\n"
              "endmodule\n"));
}

// §A.2.9 modport_declaration ::= modport modport_item { , modport_item } ;
TEST(ParserA29, BasicModportDecl) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a;\n"
      "  modport target(input a);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "target");
}

// modport_simple_ports_declaration ::=
//   port_direction modport_simple_port { , modport_simple_port }
TEST(ParserA29, MultipleSimplePortsSameDir) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a, b, c;\n"
      "  modport target(input a, b, c);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 3u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[2].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[0].name, "a");
  EXPECT_EQ(mp->ports[1].name, "b");
  EXPECT_EQ(mp->ports[2].name, "c");
}

// modport_tf_ports_declaration ::=
//   import_export modport_tf_port { , modport_tf_port }
TEST(ParserA29, ImportSingleIdentifier) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].name, "Read");
}

TEST(ParserA29, ImportMultipleIdentifiers) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read, Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].name, "Read");
  EXPECT_TRUE(mp->ports[1].is_import);
  EXPECT_EQ(mp->ports[1].name, "Write");
}

TEST(ParserA29, ImportMultiplePrototypes) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(\n"
      "    import task Read(input logic [7:0] raddr),\n"
      "           task Write(input logic [7:0] waddr)\n"
      "  );\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].prototype->name, "Read");
  EXPECT_TRUE(mp->ports[1].is_import);
  EXPECT_EQ(mp->ports[1].prototype->name, "Write");
}

// Mixed modport_ports_declarations
TEST(ParserA29, MixedDirImportExport) {
  auto r = Parse(
      "interface bus;\n"
      "  logic req, gnt;\n"
      "  modport target(\n"
      "    input req,\n"
      "    output gnt,\n"
      "    import Read,\n"
      "    export Write\n"
      "  );\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 4u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kOutput);
  EXPECT_TRUE(mp->ports[2].is_import);
  EXPECT_TRUE(mp->ports[3].is_export);
}

TEST(ParserA29, AttrOnImportPort) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  modport target((* synthesis *) import Read);\n"
              "endinterface\n"));
}

// Direction persists across simple ports (§25.5)
TEST(ParserA29, DirectionPersistsAcrossPorts) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a, b, c, d;\n"
      "  modport target(input a, b, output c, d);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 4u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[2].direction, Direction::kOutput);
  EXPECT_EQ(mp->ports[3].direction, Direction::kOutput);
}

// Empty modport (no ports) should parse
TEST(ParserA29, EmptyModport) {
  auto r = Parse(
      "interface bus;\n"
      "  modport empty();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->ports.size(), 0u);
  EXPECT_EQ(mp->name, "empty");
}

static ModuleItem *FindItemByKind(const std::vector<ModuleItem *> &items,
                                  ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// sequence_expr ::= ( sequence_expr {, sequence_match_item} ) [sequence_abbrev]
TEST(ParserA210, SequenceExpr_ParenWithMatchItems) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x = c) |-> d);\n"
              "endmodule\n"));
}

// property_list_of_arguments — mixed positional + named
TEST(ParserA210, PropertyListOfArguments_Mixed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(x, y, z); x |-> y ##1 z; endproperty\n"
              "  assert property (p(a, .y(b), .z(c)));\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupDecl_WithEmptyPortList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg();\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverageSpecOrOption_CoverSpec) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverPoint_WithDataType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint x {\n"
              "      bins low = {[0:3]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BinsOrEmpty_WithBraces) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {1};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #10: bins_or_options
// =============================================================================
TEST(ParserA211, BinsOrOptions_ValueRangeList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins low = {[0:3]};\n"
              "      bins mid = {[4:7]};\n"
              "      bins high = {[8:15]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BinsOrOptions_AutoSizedArray) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b[] = {[0:15]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BinsOrOptions_Default) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins others = default;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BinsOrOptions_DefaultSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins others = default sequence;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BinsOrOptions_SetCovergroupExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = x;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BinsOrOptions_WithWithClause) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = {[0:15]} with (item > 5);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #11: bins_keyword
// =============================================================================
TEST(ParserA211, BinsKeyword_Bins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {0};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BinsKeyword_IllegalBins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      illegal_bins bad = {255};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BinsKeyword_IgnoreBins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      ignore_bins skip = {128};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #12: trans_list
// =============================================================================
TEST(ParserA211, TransList_Single) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 => 2);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, TransList_Multiple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 => 2), (3 => 4);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #13: trans_set
// =============================================================================
TEST(ParserA211, TransSet_SingleRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 => 3);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, TransSet_MultipleRanges) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 => 3 => 5);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #14: trans_range_list
// =============================================================================
TEST(ParserA211, TransRangeList_SimpleItem) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (0 => 1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, TransRangeList_ConsecutiveRepeat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 [* 3]);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, TransRangeList_GotoRepeat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 [-> 3]);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, TransRangeList_NonConsecutiveRepeat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 [= 3]);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #15: trans_item (alias for covergroup_range_list)
// =============================================================================
TEST(ParserA211, TransItem_SingleValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (5 => 10);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, TransItem_MultipleValues) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1, 2, 3 => 4, 5);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #16: repeat_range
// =============================================================================
TEST(ParserA211, RepeatRange_SingleExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 [* 5]);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, RepeatRange_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 [* 2:5]);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #17: cover_cross
// =============================================================================
TEST(ParserA211, CoverCross_Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverCross_Labeled) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    my_cross: cross cp1, cp2;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverCross_WithIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 iff (enable);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverCross_WithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) intersect {[0:3]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #18: list_of_cross_items
// =============================================================================
TEST(ParserA211, ListOfCrossItems_Two) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, ListOfCrossItems_Three) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cp3: coverpoint c;\n"
              "    cross cp1, cp2, cp3;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #19: cross_item
// =============================================================================
TEST(ParserA211, CrossItem_CoverPointIdentifier) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp_a: coverpoint a;\n"
              "    cp_b: coverpoint b;\n"
              "    cross cp_a, cp_b;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #20: cross_body
// =============================================================================
TEST(ParserA211, CrossBody_Empty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CrossBody_WithItems) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #21: cross_body_item
// =============================================================================
TEST(ParserA211, CrossBodyItem_BinsSelection) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins ab = binsof(cp1) intersect {[0:3]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CrossBodyItem_FunctionDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      function CrossQueueType myFunc(int val);\n"
              "        return '{val};\n"
              "      endfunction\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #22: bins_selection_or_option
// =============================================================================
TEST(ParserA211, BinsSelectionOrOption_CoverageOption) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      option.weight = 5;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BinsSelectionOrOption_BinsSelection) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins selected = binsof(cp1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #23: bins_selection
// =============================================================================
TEST(ParserA211, BinsSelection_Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins my_bin = binsof(cp1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BinsSelection_WithIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) iff (enable);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #24: select_expression
// =============================================================================
TEST(ParserA211, SelectExpression_SelectCondition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, SelectExpression_Negated) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = !binsof(cp1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, SelectExpression_And) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) && binsof(cp2);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, SelectExpression_Or) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) || binsof(cp2);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, SelectExpression_Parenthesized) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = (binsof(cp1) && binsof(cp2));\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #25: select_condition
// =============================================================================
TEST(ParserA211, SelectCondition_Binsof) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, SelectCondition_BinsofIntersect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) intersect {[0:3]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #26: bins_expression
// =============================================================================
TEST(ParserA211, BinsExpression_Variable) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BinsExpression_CoverPointDotBin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1.low);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #27: covergroup_range_list
// =============================================================================
TEST(ParserA211, CovergroupRangeList_Single) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {5};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupRangeList_Multiple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {1, 2, 3, 4, 5};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupRangeList_MixedRanges) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {1, [3:5], 8, [10:15]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #28: covergroup_value_range
// =============================================================================
TEST(ParserA211, CovergroupValueRange_SingleValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {42};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupValueRange_ClosedRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {[0:255]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupValueRange_OpenLow) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {[$:100]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupValueRange_OpenHigh) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {[100:$]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #29: with_covergroup_expression
// =============================================================================
TEST(ParserA211, WithCovergroupExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = {[0:255]} with (item > 10);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #30: set_covergroup_expression
// =============================================================================
TEST(ParserA211, SetCovergroupExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = x;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #31: integer_covergroup_expression
// =============================================================================
TEST(ParserA211, IntegerCovergroupExpression_Expr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b[4] = {[0:15]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #32: cross_set_expression
// =============================================================================
TEST(ParserA211, CrossSetExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) intersect {[0:7]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #33: covergroup_expression
// =============================================================================
TEST(ParserA211, CovergroupExpression_Literal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {10};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupExpression_BinaryOp) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {a + b};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// Additional comprehensive tests
// =============================================================================
TEST(ParserA211, FullCovergroup_MultipleElements) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(posedge clk);\n"
              "    option.auto_bin_max = 64;\n"
              "    cp_addr: coverpoint addr {\n"
              "      bins low = {[0:63]};\n"
              "      bins mid = {[64:191]};\n"
              "      bins high = {[192:255]};\n"
              "    }\n"
              "    cp_data: coverpoint data;\n"
              "    cross cp_addr, cp_data;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_AllBinTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {0, 1, 2};\n"
              "      bins b[3] = {[0:8]};\n"
              "      bins c[] = {[0:15]};\n"
              "      bins d = default;\n"
              "      bins e = default sequence;\n"
              "      wildcard bins w = {4'b1??0};\n"
              "      illegal_bins bad = {255};\n"
              "      ignore_bins skip = {128};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_TransitionBins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t1 = (0 => 1 => 2);\n"
              "      bins t2 = (0 => 1), (2 => 3);\n"
              "      bins t3 = (1 [* 3]);\n"
              "      bins t4 = (1 [-> 2]);\n"
              "      bins t5 = (1 [= 2]);\n"
              "      bins t6 = (1 [* 2:5]);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_CrossWithBinsSelection) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel1 = binsof(cp1) intersect {[0:3]};\n"
              "      bins sel2 = !binsof(cp2);\n"
              "      bins sel3 = binsof(cp1) && binsof(cp2);\n"
              "      ignore_bins ig = binsof(cp1) intersect {255};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_MultipleCoverpoints) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(posedge clk);\n"
              "    type_option.weight = 2;\n"
              "    cp1: coverpoint a iff (enable);\n"
              "    cp2: coverpoint b;\n"
              "    cp3: coverpoint c {\n"
              "      bins low = {[0:3]};\n"
              "      bins high = {[4:7]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_ExtendsWithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup child extends parent;\n"
              "    coverpoint z;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_SampleFunctionWithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg with function sample(int val);\n"
              "    coverpoint val {\n"
              "      bins low = {[0:127]};\n"
              "      bins high = {[128:255]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_PortsWithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg(ref int x, input int threshold);\n"
              "    coverpoint x {\n"
              "      bins below = {[0:threshold]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_EmptyCrossBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {}\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_MultipleOptions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.auto_bin_max = 64;\n"
              "    option.weight = 2;\n"
              "    option.goal = 95;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_InPackage) {
  EXPECT_TRUE(
      ParseOk("package p;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endpackage\n"));
}

TEST(ParserA211, CoverGroup_NegedgeEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(negedge rst_n);\n"
              "    coverpoint state;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_ValueRangesInBins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {[$:50]};\n"
              "      bins b = {[51:100]};\n"
              "      bins c = {[101:$]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_CrossThreeItems) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    a_cp: coverpoint a;\n"
              "    b_cp: coverpoint b;\n"
              "    c_cp: coverpoint c;\n"
              "    cross a_cp, b_cp, c_cp;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_BinsWithCoverPointRef) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = {[0:15]} with (item < 10);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_WildcardIllegalIgnore) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      wildcard bins even = {4'b???0};\n"
              "      wildcard bins odd = {4'b???1};\n"
              "      illegal_bins overflow = {[200:255]};\n"
              "      ignore_bins reset = {0};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_ASTVerification) {
  auto r = Parse(
      "module m;\n"
      "  covergroup my_cg @(posedge clk);\n"
      "    coverpoint addr;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "my_cg");
  EXPECT_EQ(item->kind, ModuleItemKind::kCovergroupDecl);
  EXPECT_TRUE(item->loc.IsValid());
}

TEST(ParserA211, CoverGroup_ExtendsASTVerification) {
  auto r = Parse(
      "module m;\n"
      "  covergroup child_cg extends parent_cg;\n"
      "    coverpoint z;\n"
      "  endgroup : child_cg\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "child_cg");
}

TEST(ParserA211, CoverGroup_SampleFunctionASTVerification) {
  auto r = Parse(
      "module m;\n"
      "  covergroup sampled_cg with function sample(int data);\n"
      "    coverpoint data;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "sampled_cg");
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
  auto *item =
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
  auto *item =
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
  auto *item =
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
  auto *item =
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
  for (auto *item : r.cu->modules[0]->items) {
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
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "foo");
}

TEST(ParserA212, LetIdentifier_Escaped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let \\my+let = 1;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetIdentifier_Underscore) {
  auto r = Parse(
      "module m;\n"
      "  let _my_let_123 = 0;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_my_let_123");
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
  auto *item =
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
  auto *item =
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
  auto *item =
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
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(ParserA212, LetPortItem_ExplicitType) {
  auto r = Parse(
      "module m;\n"
      "  let f(logic [15:0] val) = val;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "val");
}

TEST(ParserA212, LetPortItem_WithDefault) {
  auto r = Parse(
      "module m;\n"
      "  let f(x = 42) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

TEST(ParserA212, LetPortItem_NoDefault) {
  auto r = Parse(
      "module m;\n"
      "  let f(x) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->func_args[0].default_value, nullptr);
}

TEST(ParserA212, LetPortItem_WithUnpackedDim) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(logic x [3:0]) = x[0];\n"
              "endmodule\n"));
}

TEST(ParserA212, LetPortItem_TypedWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  let at_least(logic sig, logic rst = 1'b0) = rst || sig;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].default_value, nullptr);
  EXPECT_NE(item->func_args[1].default_value, nullptr);
}

TEST(ParserA212, LetPortItem_IntType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(int a, int b) = a * b;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetPortItem_BitType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(bit [7:0] x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetPortItem_RegType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(reg [3:0] r) = r;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetPortItem_AttributeInstance) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* my_attr *) logic x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetPortItem_AttributeInstanceMultiple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* a = 1 *) x, (* b *) y) = x + y;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetPortItem_AttributeWithValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* attr = 5 *) int x) = x;\n"
              "endmodule\n"));
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
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "a");
}

TEST(ParserA212, LetFormalType_Implicit) {
  auto r = Parse(
      "module m;\n"
      "  let f(x) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(ParserA212, LetFormalType_Logic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(logic x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetFormalType_LogicPacked) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(logic [31:0] x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetFormalType_Integer) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(integer x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetFormalType_Real) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(real x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetFormalType_SignedImplicit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(signed [7:0] x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetFormalType_UnsignedImplicit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(unsigned [7:0] x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetFormalType_MixedUntypedAndTyped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(untyped a, logic [7:0] b) = b;\n"
              "endmodule\n"));
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

TEST(ParserA212, LetExpr_NoArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let val = 42;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = val;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetExpr_EmptyParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let val() = 42;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = val();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetExpr_PackageScope) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  let add(x, y) = x + y;\n"
              "endpackage\n"
              "module m;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = pkg::add(1, 2);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetExpr_InAssign) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let add(a, b) = a + b;\n"
              "  logic [7:0] w;\n"
              "  assign w = add(8'd1, 8'd2);\n"
              "endmodule\n"));
}

TEST(ParserA212, LetExpr_Nested) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let inc(x) = x + 1;\n"
              "  let dbl(x) = x * 2;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = dbl(inc(3));\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetExpr_InConditional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let valid(x) = x != 0;\n"
              "  initial begin\n"
              "    int a;\n"
              "    if (valid(a)) a = 0;\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// A.2.12 Production #7: let_list_of_arguments
// let_list_of_arguments ::=
//     [let_actual_arg] { , [let_actual_arg] }
//         { , .identifier ( [let_actual_arg] ) }
//   | .identifier ( [let_actual_arg] ) { , .identifier ( [let_actual_arg] ) }
// =============================================================================
TEST(ParserA212, LetArgs_SinglePositional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(5);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetArgs_MultiplePositional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(a, b, c) = a + b + c;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(1, 2, 3);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetArgs_Named) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(a, b) = a + b;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(.a(1), .b(2));\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetArgs_DefaultOmitted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(a, b = 10) = a + b;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(5);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetArgs_AllNamed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let arb(request, valid, override) = "
              "    |(request & valid) || override;\n"
              "  initial begin\n"
              "    logic result;\n"
              "    result = arb(.request(2'b11), .valid(2'b10),"
              " .override(1'b0));\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetArgs_ExprInArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x, y) = x + y;\n"
              "  initial begin\n"
              "    int a, b, z;\n"
              "    z = f(a * 2, b + 1);\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// A.2.12 Production #8: let_actual_arg
// let_actual_arg ::= expression
// =============================================================================
TEST(ParserA212, LetActualArg_Literal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(42);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetActualArg_Variable) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int a, z;\n"
              "    z = f(a);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetActualArg_BinaryExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int a, b, z;\n"
              "    z = f(a + b);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetActualArg_Ternary) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int a, z;\n"
              "    z = f(a > 0 ? a : -a);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetActualArg_Concatenation) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    logic [7:0] z;\n"
              "    z = f({4'b0, 4'b1});\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetActualArg_FunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int inc(int x); return x + 1; endfunction\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(inc(5));\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// A.3 -- Primitive instances (gate_instantiation)
// =============================================================================
TEST(ParserAnnexA, A3GateInstNInput) {
  auto r = Parse(
      "module m;\n"
      "  and g1(y, a, b, c);\n"
      "  nand g2(y2, a, b);\n"
      "  xor g3(y3, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int gate_count = 0;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGateInst) gate_count++;
  }
  EXPECT_EQ(gate_count, 3);
}

TEST(ParserAnnexA, A3GateInstWithStrengthAndDelay) {
  auto r = Parse("module m; and (strong0, weak1) #5 g(y, a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

static ModuleItem *FindGateByKind(const std::vector<ModuleItem *> &items,
                                  GateKind kind) {
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kGateInst && item->gate_kind == kind)
      return item;
  }
  return nullptr;
}

static std::vector<ModuleItem *> FindAllGates(
    const std::vector<ModuleItem *> &items) {
  std::vector<ModuleItem *> gates;
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kGateInst) gates.push_back(item);
  }
  return gates;
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (cmos_switchtype alternative)
// gate_instantiation ::=
//   cmos_switchtype [delay3] cmos_switch_instance {, cmos_switch_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_CmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  cmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, GateInst_RcmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  rcmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, GateInst_CmosWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  cmos #5 (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
}

TEST(ParserA301, GateInst_CmosWithDelay3) {
  auto r = Parse(
      "module m;\n"
      "  cmos #(2, 3, 4) (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_NE(g->gate_delay_fall, nullptr);
  EXPECT_NE(g->gate_delay_decay, nullptr);
}

TEST(ParserA301, GateInst_CmosMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(o1, i1, n1, p1), c2(o2, i2, n2, p2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->gate_inst_name, "c1");
  EXPECT_EQ(gates[1]->gate_inst_name, "c2");
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (mos_switchtype alternative)
// gate_instantiation ::=
//   mos_switchtype [delay3] mos_switch_instance {, mos_switch_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_NmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  nmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_PmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  pmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_RnmosBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rnmos (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_RpmosBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rpmos (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_MosWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  nmos #10 n1(out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_inst_name, "n1");
}

TEST(ParserA301, GateInst_MosMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pmos p1(o1, i1, c1), p2(o2, i2, c2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (enable_gatetype alternative)
// gate_instantiation ::=
//   enable_gatetype [drive_strength] [delay3] enable_gate_instance
//                   {, enable_gate_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_Bufif0Basic) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_Bufif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif1 (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_Notif0Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  notif0 (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_Notif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  notif1 (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_EnableWithStrength) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (strong0, pull1) b1(out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
}

TEST(ParserA301, GateInst_EnableWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  notif1 #(3, 4, 5) (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_NE(g->gate_delay_fall, nullptr);
  EXPECT_NE(g->gate_delay_decay, nullptr);
}

TEST(ParserA301, GateInst_EnableWithStrengthAndDelay) {
  auto r = Parse(
      "module m;\n"
      "  bufif1 (weak0, weak1) #7 b1(out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif1);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
  EXPECT_NE(g->gate_delay, nullptr);
}

TEST(ParserA301, GateInst_EnableMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 b1(o1, i1, c1), b2(o2, i2, c2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (n_input_gatetype alternative)
// gate_instantiation ::=
//   n_input_gatetype [drive_strength] [delay2] n_input_gate_instance
//                    {, n_input_gate_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_AndBasic) {
  auto r = Parse(
      "module m;\n"
      "  and (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_NandBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nand (out, a, b);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_OrBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  or (out, a, b);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_NorBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nor (out, a, b);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_XorBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  xor (out, a, b);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_XnorBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  xnor (out, a, b);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_NInputWithStrength) {
  auto r = Parse(
      "module m;\n"
      "  and (pull0, pull1) a1(out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
}

TEST(ParserA301, GateInst_NInputWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  or #(3, 5) o1(out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kOr);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_NE(g->gate_delay_fall, nullptr);
}

TEST(ParserA301, GateInst_NInputMultipleInputs) {
  auto r = Parse(
      "module m;\n"
      "  and (out, a, b, c, d);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 5u);
}

TEST(ParserA301, GateInst_NInputMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  and a1(o1, i1, i2), a2(o2, i3, i4);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->gate_inst_name, "a1");
  EXPECT_EQ(gates[1]->gate_inst_name, "a2");
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (n_output_gatetype alternative)
// gate_instantiation ::=
//   n_output_gatetype [drive_strength] [delay2] n_output_gate_instance
//                     {, n_output_gate_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_BufBasic) {
  auto r = Parse(
      "module m;\n"
      "  buf (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA301, GateInst_NotBasic) {
  auto r = Parse(
      "module m;\n"
      "  not (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA301, GateInst_NOutputMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  buf (o1, o2, o3, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, GateInst_NOutputWithStrength) {
  auto r = Parse(
      "module m;\n"
      "  buf (strong0, strong1) b1(out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
}

TEST(ParserA301, GateInst_NOutputWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  not #(4, 6) n1(out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_NE(g->gate_delay_fall, nullptr);
}

TEST(ParserA301, GateInst_NOutputMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  buf b1(o1, i1), b2(o2, i2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (pass_en_switchtype alternative)
// gate_instantiation ::=
//   pass_en_switchtype [delay2] pass_enable_switch_instance
//                      {, pass_enable_switch_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_Tranif0Basic) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_Tranif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tranif1 (io1, io2, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_Rtranif0Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtranif0 (io1, io2, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_Rtranif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtranif1 (io1, io2, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_PassEnWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 #(3, 5) t1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
}

TEST(ParserA301, GateInst_PassEnMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 t1(a1, b1, c1), t2(a2, b2, c2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (pass_switchtype alternative)
// gate_instantiation ::=
//   pass_switchtype pass_switch_instance {, pass_switch_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_TranBasic) {
  auto r = Parse(
      "module m;\n"
      "  tran (io1, io2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA301, GateInst_RtranBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtran (io1, io2);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_PassSwitchMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  tran t1(a1, b1), t2(a2, b2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (pulldown alternative)
// gate_instantiation ::=
//   pulldown [pulldown_strength] pull_gate_instance {, pull_gate_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_PulldownBasic) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(ParserA301, GateInst_PulldownNamed) {
  auto r = Parse(
      "module m;\n"
      "  pulldown pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pd1");
}

TEST(ParserA301, GateInst_PulldownMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pulldown pd1(a), pd2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (pullup alternative)
// gate_instantiation ::=
//   pullup [pullup_strength] pull_gate_instance {, pull_gate_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_PullupBasic) {
  auto r = Parse(
      "module m;\n"
      "  pullup (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(ParserA301, GateInst_PullupNamed) {
  auto r = Parse(
      "module m;\n"
      "  pullup pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pu1");
}

TEST(ParserA301, GateInst_PullupMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pullup pu1(a), pu2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

// =============================================================================
// A.3.1 Production #2: cmos_switch_instance
// cmos_switch_instance ::= [name_of_instance]
//   ( output_terminal , input_terminal , ncontrol_terminal , pcontrol_terminal
//   )
// =============================================================================
TEST(ParserA301, CmosSwitchInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  cmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, CmosSwitchInst_Named) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "c1");
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, CmosSwitchInst_RcmosNamed) {
  auto r = Parse(
      "module m;\n"
      "  rcmos rc1(out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rc1");
}

// =============================================================================
// A.3.1 Production #3: enable_gate_instance
// enable_gate_instance ::= [name_of_instance]
//   ( output_terminal , input_terminal , enable_terminal )
// =============================================================================
TEST(ParserA301, EnableGateInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, EnableGateInst_Named) {
  auto r = Parse(
      "module m;\n"
      "  notif1 n1(out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "n1");
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

// =============================================================================
// A.3.1 Production #4: mos_switch_instance
// mos_switch_instance ::= [name_of_instance]
//   ( output_terminal , input_terminal , enable_terminal )
// =============================================================================
TEST(ParserA301, MosSwitchInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  nmos (out, in, gate);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

TEST(ParserA301, MosSwitchInst_Named) {
  auto r = Parse(
      "module m;\n"
      "  pmos p1(out, in, gate);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "p1");
}

// =============================================================================
// A.3.1 Production #5: n_input_gate_instance
// n_input_gate_instance ::= [name_of_instance]
//   ( output_terminal , input_terminal {, input_terminal} )
// =============================================================================
TEST(ParserA301, NInputGateInst_TwoInputs) {
  auto r = Parse(
      "module m;\n"
      "  and a1(out, in1, in2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "a1");
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, NInputGateInst_FourInputs) {
  auto r = Parse(
      "module m;\n"
      "  nand n1(out, a, b, c, d);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNand);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 5u);
}

TEST(ParserA301, NInputGateInst_EightInputs) {
  auto r = Parse(
      "module m;\n"
      "  xor x1(out, a, b, c, d, e, f, g, h);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kXor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 9u);
}

TEST(ParserA301, NInputGateInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  or (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kOr);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

// =============================================================================
// A.3.1 Production #6: n_output_gate_instance
// n_output_gate_instance ::= [name_of_instance]
//   ( output_terminal {, output_terminal} , input_terminal )
// =============================================================================
TEST(ParserA301, NOutputGateInst_SingleOutput) {
  auto r = Parse(
      "module m;\n"
      "  buf b1(out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA301, NOutputGateInst_ThreeOutputs) {
  auto r = Parse(
      "module m;\n"
      "  not n1(o1, o2, o3, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, NOutputGateInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  buf (o1, o2, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

// =============================================================================
// A.3.1 Production #7: pass_switch_instance
// pass_switch_instance ::= [name_of_instance] ( inout_terminal , inout_terminal
// )
// =============================================================================
TEST(ParserA301, PassSwitchInst_TranNamed) {
  auto r = Parse(
      "module m;\n"
      "  tran t1(io1, io2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "t1");
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA301, PassSwitchInst_RtranNamed) {
  auto r = Parse(
      "module m;\n"
      "  rtran rt1(io1, io2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rt1");
}

TEST(ParserA301, PassSwitchInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  tran (io1, io2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

// =============================================================================
// A.3.1 Production #8: pass_enable_switch_instance
// pass_enable_switch_instance ::= [name_of_instance]
//   ( inout_terminal , inout_terminal , enable_terminal )
// =============================================================================
TEST(ParserA301, PassEnSwitchInst_Tranif0Named) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 t1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "t1");
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, PassEnSwitchInst_Tranif1Named) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 t1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "t1");
}

TEST(ParserA301, PassEnSwitchInst_Rtranif0Named) {
  auto r = Parse(
      "module m;\n"
      "  rtranif0 rt1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rt1");
}

TEST(ParserA301, PassEnSwitchInst_Rtranif1Named) {
  auto r = Parse(
      "module m;\n"
      "  rtranif1 rt1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rt1");
}

TEST(ParserA301, PassEnSwitchInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

// =============================================================================
// A.3.1 Production #9: pull_gate_instance
// pull_gate_instance ::= [name_of_instance] ( output_terminal )
// =============================================================================
TEST(ParserA301, PullGateInst_PullupNamed) {
  auto r = Parse(
      "module m;\n"
      "  pullup pu1(net1);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pu1");
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(ParserA301, PullGateInst_PulldownNamed) {
  auto r = Parse(
      "module m;\n"
      "  pulldown pd1(net1);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pd1");
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(ParserA301, PullGateInst_PullupUnnamed) {
  auto r = Parse(
      "module m;\n"
      "  pullup (net1);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

// =============================================================================
// Additional gate_instantiation combinations
// =============================================================================
TEST(ParserA301, GateInst_AllNInputGateTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  and  a1(o, i1, i2);\n"
              "  nand n1(o, i1, i2);\n"
              "  or   o1(o, i1, i2);\n"
              "  nor  r1(o, i1, i2);\n"
              "  xor  x1(o, i1, i2);\n"
              "  xnor z1(o, i1, i2);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_AllEnableGateTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif0 b0(o, i, c);\n"
              "  bufif1 b1(o, i, c);\n"
              "  notif0 n0(o, i, c);\n"
              "  notif1 n1(o, i, c);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_AllMosSwitchTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nmos  n1(o, i, g);\n"
              "  pmos  p1(o, i, g);\n"
              "  rnmos rn1(o, i, g);\n"
              "  rpmos rp1(o, i, g);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_AllCmosSwitchTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  cmos  c1(o, i, n, p);\n"
              "  rcmos rc1(o, i, n, p);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_AllPassSwitchTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tran  t1(a, b);\n"
              "  rtran rt1(a, b);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_AllPassEnSwitchTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tranif0  t0(a, b, c);\n"
              "  tranif1  t1(a, b, c);\n"
              "  rtranif0 rt0(a, b, c);\n"
              "  rtranif1 rt1(a, b, c);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_StrengthOrder_Strength1First) {
  auto r = Parse(
      "module m;\n"
      "  and (pull1, strong0) a1(out, in1, in2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
}

TEST(ParserA301, GateInst_DelayWithMinTypMax) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  and #(1:2:3, 4:5:6) a1(out, in1, in2);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_ComplexTerminalExpressions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  and a1(out[0], in1[3:0], in2[7:4]);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_NamedUnnamedMixedInMulti) {
  auto r = Parse(
      "module m;\n"
      "  and a1(o1, i1, i2), a2(o2, i3, i4), a3(o3, i5, i6);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 3u);
  EXPECT_EQ(gates[0]->gate_inst_name, "a1");
  EXPECT_EQ(gates[1]->gate_inst_name, "a2");
  EXPECT_EQ(gates[2]->gate_inst_name, "a3");
}

TEST(ParserA301, GateInst_SharedStrengthAcrossInstances) {
  auto r = Parse(
      "module m;\n"
      "  and (weak0, weak1) a1(o1, i1, i2), a2(o2, i3, i4);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, gates[1]->drive_strength0);
  EXPECT_EQ(gates[0]->drive_strength1, gates[1]->drive_strength1);
}

TEST(ParserA301, GateInst_SharedDelayAcrossInstances) {
  auto r = Parse(
      "module m;\n"
      "  or #5 o1(out1, a, b), o2(out2, c, d);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_NE(gates[0]->gate_delay, nullptr);
  EXPECT_NE(gates[1]->gate_delay, nullptr);
}

// =============================================================================
// A.3.2 Primitive strengths
//
// pulldown_strength ::=
//   ( strength0 , strength1 )
//   | ( strength1 , strength0 )
//   | ( strength0 )
//
// pullup_strength ::=
//   ( strength0 , strength1 )
//   | ( strength1 , strength0 )
//   | ( strength1 )
// =============================================================================
// -----------------------------------------------------------------------------
// Production #1: pulldown_strength
// pulldown_strength ::= ( strength0 , strength1 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PulldownStrength_Strength0Strength1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (strong0, pull1) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);  // strong0
  EXPECT_EQ(g->drive_strength1, 3u);  // pull1
  EXPECT_EQ(g->gate_inst_name, "pd1");
}

TEST(ParserA302, PulldownStrength_Supply0Weak1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (supply0, weak1) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 5u);  // supply0
  EXPECT_EQ(g->drive_strength1, 2u);  // weak1
}

TEST(ParserA302, PulldownStrength_Pull0Highz1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull0, highz1) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 3u);  // pull0
  EXPECT_EQ(g->drive_strength1, 1u);  // highz1
}

// -----------------------------------------------------------------------------
// Production #1: pulldown_strength
// pulldown_strength ::= ( strength1 , strength0 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PulldownStrength_Strength1Strength0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull1, strong0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);  // strong0
  EXPECT_EQ(g->drive_strength1, 3u);  // pull1
}

TEST(ParserA302, PulldownStrength_Highz1Supply0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (highz1, supply0) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 5u);  // supply0
  EXPECT_EQ(g->drive_strength1, 1u);  // highz1
}

// -----------------------------------------------------------------------------
// Production #1: pulldown_strength
// pulldown_strength ::= ( strength0 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PulldownStrength_SingleStrength0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (strong0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);  // strong0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

TEST(ParserA302, PulldownStrength_SingleSupply0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (supply0) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 5u);  // supply0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

TEST(ParserA302, PulldownStrength_SingleWeak0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (weak0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 2u);  // weak0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

TEST(ParserA302, PulldownStrength_SinglePull0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 3u);  // pull0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

TEST(ParserA302, PulldownStrength_SingleHighz0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (highz0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 1u);  // highz0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

// -----------------------------------------------------------------------------
// Production #2: pullup_strength
// pullup_strength ::= ( strength0 , strength1 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PullupStrength_Strength0Strength1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (strong0, pull1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);  // strong0
  EXPECT_EQ(g->drive_strength1, 3u);  // pull1
  EXPECT_EQ(g->gate_inst_name, "pu1");
}

TEST(ParserA302, PullupStrength_Weak0Supply1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (weak0, supply1) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 2u);  // weak0
  EXPECT_EQ(g->drive_strength1, 5u);  // supply1
}

// -----------------------------------------------------------------------------
// Production #2: pullup_strength
// pullup_strength ::= ( strength1 , strength0 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PullupStrength_Strength1Strength0) {
  auto r = Parse(
      "module m;\n"
      "  pullup (supply1, weak0) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 2u);  // weak0
  EXPECT_EQ(g->drive_strength1, 5u);  // supply1
}

TEST(ParserA302, PullupStrength_Highz1Strong0) {
  auto r = Parse(
      "module m;\n"
      "  pullup (highz1, strong0) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);  // strong0
  EXPECT_EQ(g->drive_strength1, 1u);  // highz1
}

// -----------------------------------------------------------------------------
// Production #2: pullup_strength
// pullup_strength ::= ( strength1 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PullupStrength_SingleStrength1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (strong1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);  // none
  EXPECT_EQ(g->drive_strength1, 4u);  // strong1
}

TEST(ParserA302, PullupStrength_SingleSupply1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (supply1) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);  // none
  EXPECT_EQ(g->drive_strength1, 5u);  // supply1
}

TEST(ParserA302, PullupStrength_SingleWeak1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (weak1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);  // none
  EXPECT_EQ(g->drive_strength1, 2u);  // weak1
}

TEST(ParserA302, PullupStrength_SinglePull1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (pull1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);  // none
  EXPECT_EQ(g->drive_strength1, 3u);  // pull1
}

TEST(ParserA302, PullupStrength_SingleHighz1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (highz1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);  // none
  EXPECT_EQ(g->drive_strength1, 1u);  // highz1
}

// -----------------------------------------------------------------------------
// Combination: strength with multiple instances
// -----------------------------------------------------------------------------
TEST(ParserA302, PulldownStrength_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (strong0, weak1) pd1(a), pd2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 4u);  // strong0
  EXPECT_EQ(gates[0]->drive_strength1, 2u);  // weak1
  EXPECT_EQ(gates[1]->drive_strength0, 4u);  // strong0
  EXPECT_EQ(gates[1]->drive_strength1, 2u);  // weak1
}

TEST(ParserA302, PullupStrength_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pullup (weak0, strong1) pu1(a), pu2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 2u);  // weak0
  EXPECT_EQ(gates[0]->drive_strength1, 4u);  // strong1
  EXPECT_EQ(gates[1]->drive_strength0, 2u);  // weak0
  EXPECT_EQ(gates[1]->drive_strength1, 4u);  // strong1
}

TEST(ParserA302, PulldownStrength_SingleStrength0_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull0) pd1(a), pd2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 3u);  // pull0
  EXPECT_EQ(gates[0]->drive_strength1, 0u);  // none
  EXPECT_EQ(gates[1]->drive_strength0, 3u);  // pull0
  EXPECT_EQ(gates[1]->drive_strength1, 0u);  // none
}

TEST(ParserA302, PullupStrength_SingleStrength1_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pullup (pull1) pu1(a), pu2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 0u);  // none
  EXPECT_EQ(gates[0]->drive_strength1, 3u);  // pull1
  EXPECT_EQ(gates[1]->drive_strength0, 0u);  // none
  EXPECT_EQ(gates[1]->drive_strength1, 3u);  // pull1
}

// -----------------------------------------------------------------------------
// All strength0 values exercised in pulldown_strength
// -----------------------------------------------------------------------------
TEST(ParserA302, PulldownStrength_AllStrength0Values) {
  // highz0=1, weak0=2, pull0=3, strong0=4, supply0=5
  EXPECT_TRUE(ParseOk("module m; pulldown (highz0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (weak0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (pull0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (strong0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (supply0) (out); endmodule"));
}

// -----------------------------------------------------------------------------
// All strength1 values exercised in pullup_strength
// -----------------------------------------------------------------------------
TEST(ParserA302, PullupStrength_AllStrength1Values) {
  // highz1=1, weak1=2, pull1=3, strong1=4, supply1=5
  EXPECT_TRUE(ParseOk("module m; pullup (highz1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (weak1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (pull1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (strong1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (supply1) (out); endmodule"));
}

}  // namespace
