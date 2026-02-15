#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

}  // namespace

// =============================================================================
// A.2.1.1 Module parameter declarations
// =============================================================================

// --- local_parameter_declaration ---
// localparam data_type_or_implicit list_of_param_assignments

TEST(ParserA211, LocalparamExplicitType) {
  auto r = Parse("module m; localparam int X = 5; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "X");
}

TEST(ParserA211, LocalparamImplicitType) {
  auto r = Parse("module m; localparam X = 42; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "X");
}

TEST(ParserA211, LocalparamPackedDimImplicit) {
  auto r = Parse("module m; localparam [7:0] MASK = 8'hFF; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

// localparam type_parameter_declaration

TEST(ParserA211, LocalparamTypeParam) {
  auto r = Parse("module m; localparam type T = int; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVoid);
}

// --- parameter_declaration ---
// parameter data_type_or_implicit list_of_param_assignments

TEST(ParserA211, ParameterExplicitType) {
  auto r = Parse("module m; parameter int WIDTH = 8; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "WIDTH");
}

TEST(ParserA211, ParameterImplicitType) {
  auto r = Parse("module m; parameter SIZE = 16; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
}

TEST(ParserA211, ParameterPackedDim) {
  auto r = Parse("module m; parameter [31:0] ADDR = 0; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

// parameter type_parameter_declaration

TEST(ParserA211, ParameterTypeParam) {
  auto r = Parse("module m; parameter type BusType = logic [7:0]; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVoid);
}

// parameter data_type_or_implicit: various data types

TEST(ParserA211, ParameterStringType) {
  auto r = Parse("module m; parameter string NAME = \"hello\"; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA211, ParameterRealType) {
  auto r = Parse("module m; parameter real PI = 3.14; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- type_parameter_declaration ---
// type [ forward_type ] list_of_type_assignments

TEST(ParserA211, TypeParamForwardEnum) {
  auto r = Parse("module m; parameter type enum E = my_enum_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "E");
}

TEST(ParserA211, TypeParamForwardStruct) {
  auto r = Parse("module m; parameter type struct S = my_struct_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "S");
}

TEST(ParserA211, TypeParamForwardUnion) {
  auto r = Parse("module m; parameter type union U = my_union_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "U");
}

TEST(ParserA211, TypeParamForwardClass) {
  auto r = Parse("module m; parameter type class C = my_class_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "C");
}

TEST(ParserA211, TypeParamForwardInterfaceClass) {
  auto r = Parse(
      "module m;\n"
      "  parameter type interface class IC = my_ifc_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "IC");
}

// list_of_param_assignments: multiple comma-separated params

TEST(ParserA211, ListOfParamAssignments) {
  auto r = Parse("module m; parameter int A = 1, B = 2, C = 3; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int param_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) param_count++;
  }
  EXPECT_GE(param_count, 3);
}

TEST(ParserA211, ListOfLocalparamAssignments) {
  auto r = Parse("module m; localparam int X = 10, Y = 20; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int param_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) param_count++;
  }
  EXPECT_GE(param_count, 2);
}

// list_of_type_assignments: multiple type params

TEST(ParserA211, ListOfTypeAssignments) {
  auto r = Parse("module m; parameter type T1 = int, T2 = real; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int param_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) param_count++;
  }
  EXPECT_GE(param_count, 2);
}

// --- specparam_declaration ---
// specparam [ packed_dimension ] list_of_specparam_assignments ;

TEST(ParserA211, SpecparamBasic) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 100; endspecify\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA211, SpecparamPackedDim) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam [31:0] tDELAY = 50; endspecify\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA211, SpecparamMultipleAssignments) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 100, tFALL = 50; endspecify\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// specparam as non_port_module_item (outside specify)

TEST(ParserA211, SpecparamOutsideSpecify) {
  auto r = Parse("module m; specparam tPD = 10; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kSpecparam);
}

// param_assignment with unpacked dimensions (no default value)
// param_assignment ::= parameter_identifier { variable_dimension } [ = ... ]

TEST(ParserA211, ParamAssignmentNoDefault) {
  auto r = Parse("module m #(parameter int P)(); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.2.1.2 Port declarations
// =============================================================================

// --- inout_declaration ---
// inout net_port_type list_of_port_identifiers

TEST(ParserA212, InoutWireNetType) {
  auto r = Parse("module m(inout wire a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_EQ(port.name, "a");
}

TEST(ParserA212, InoutImplicitType) {
  auto r = Parse("module m(inout a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
}

TEST(ParserA212, InoutPackedDim) {
  auto r = Parse("module m(inout [7:0] a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ParserA212, InoutUnpackedDim) {
  auto r = Parse("module m(inout logic a [3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ParserA212, InoutNonAnsi) {
  auto r = Parse("module m(a); inout wire [7:0] a; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
}

// --- input_declaration ---
// input net_port_type list_of_port_identifiers
// | input variable_port_type list_of_variable_identifiers

TEST(ParserA212, InputNetPortType) {
  auto r = Parse("module m(input wire [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ParserA212, InputVariablePortTypeLogic) {
  auto r = Parse("module m(input logic [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
}

TEST(ParserA212, InputVariablePortTypeVar) {
  // variable_port_type ::= var_data_type
  // var_data_type ::= var data_type_or_implicit
  auto r = Parse("module m(input var logic d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(ParserA212, InputUnpackedDim) {
  // list_of_variable_identifiers: variable_identifier { variable_dimension }
  auto r = Parse("module m(input logic d [3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ParserA212, InputNonAnsiMultiple) {
  // Non-ANSI: input net_port_type list_of_port_identifiers (comma list)
  auto r = Parse("module m(a, b); input wire [7:0] a, b; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto& port : r.cu->modules[0]->ports) {
    EXPECT_EQ(port.direction, Direction::kInput);
  }
}

// --- output_declaration ---
// output net_port_type list_of_port_identifiers
// | output variable_port_type list_of_variable_port_identifiers

TEST(ParserA212, OutputNetPortType) {
  auto r = Parse("module m(output wire q); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(ParserA212, OutputVariablePortTypeReg) {
  auto r = Parse("module m(output reg q); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(ParserA212, OutputDefaultValue) {
  // list_of_variable_port_identifiers: port_id [ = constant_expression ]
  auto r = Parse("module m(output logic q = 1'b0); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_NE(port.default_value, nullptr);
}

TEST(ParserA212, OutputUnpackedDim) {
  auto r = Parse("module m(output logic q [1:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ParserA212, OutputNonAnsi) {
  auto r = Parse("module m(q); output reg q; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(ParserA212, OutputNonAnsiUnpackedDim) {
  // Non-ANSI: list_of_port_identifiers with unpacked_dimension
  auto r = Parse("module m(q); output logic q [3:0]; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
}

// --- ref_declaration ---
// ref variable_port_type list_of_variable_identifiers

TEST(ParserA212, RefDeclaration) {
  auto r = Parse("module m(ref logic [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kRef);
}

TEST(ParserA212, RefUnpackedDim) {
  auto r = Parse("module m(ref int arr [4]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

// --- interface_port_declaration ---
// interface_identifier list_of_interface_identifiers
// | interface_identifier . modport_identifier list_of_interface_identifiers
// Note: Interface ports without direction keyword in ANSI port lists are
// lexically ambiguous with non-ANSI identifier-only port lists. The parser
// treats identifier-only port lists as non-ANSI; semantic analysis resolves
// interface types. This tests the non-ANSI parsing path.

TEST(ParserA212, InterfacePortParsedAsNonAnsi) {
  // Without direction keyword, interface ports parse as non-ANSI port names.
  auto r = Parse("module m(a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kNone);
}

// --- net_port_type ---
// [ net_type ] data_type_or_implicit | interconnect implicit_data_type

TEST(ParserA212, NetPortTypeTriType) {
  auto r = Parse("module m(inout tri [7:0] bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "bus");
}

// --- variable_port_type ---
// var_data_type ::= data_type | var data_type_or_implicit

TEST(ParserA212, VarDataTypeExplicit) {
  // var_data_type: data_type (integer_vector_type)
  auto r = Parse("module m(input logic signed [15:0] val); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(ParserA212, VarDataTypeInt) {
  // var_data_type: data_type (integer_atom_type)
  auto r = Parse("module m(input int count); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(ParserA212, VarDataTypeString) {
  // var_data_type: data_type (non_integer_type)
  auto r = Parse("module m(input string name); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.2.1.3 Type declarations
// =============================================================================

// --- data_declaration ---
// [ const ] [ var ] [ lifetime ] data_type_or_implicit
//     list_of_variable_decl_assignments ;
// | type_declaration
// | package_import_declaration
// | nettype_declaration

TEST(ParserA213, DataDeclBasicVar) {
  auto r = Parse("module m; logic [7:0] data; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "data");
}

TEST(ParserA213, DataDeclConstVar) {
  // [const] data_type list
  auto r = Parse("module m; const int MAX = 100; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(item->data_type.is_const);
}

TEST(ParserA213, DataDeclVarPrefix) {
  // [var] data_type list
  auto r = Parse("module m; var logic x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
}

TEST(ParserA213, DataDeclLifetimeAutomatic) {
  // [lifetime] data_type list — automatic qualifier in module body
  auto r = Parse("module m; automatic int counter; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(item->is_automatic);
}

TEST(ParserA213, DataDeclLifetimeStatic) {
  // [lifetime] data_type list — static qualifier in module body
  auto r = Parse("module m; static int counter; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(item->is_static);
}

TEST(ParserA213, DataDeclMultipleAssign) {
  // list_of_variable_decl_assignments: multiple names
  auto r = Parse("module m; int a = 1, b = 2; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) count++;
  }
  EXPECT_GE(count, 2);
}

TEST(ParserA213, DataDeclTypeDeclaration) {
  // type_declaration alternative
  auto r = Parse("module m; typedef int my_int_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
}

TEST(ParserA213, DataDeclPackageImport) {
  // package_import_declaration alternative
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::*; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA213, DataDeclNettypeDeclaration) {
  // nettype_declaration alternative
  auto r = Parse("module m; nettype logic my_net; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
}

// --- package_import_declaration ---
// import package_import_item { , package_import_item } ;

TEST(ParserA213, PackageImportSingle) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::foo; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "pkg");
  EXPECT_EQ(item->import_item.item_name, "foo");
}

TEST(ParserA213, PackageImportWildcard) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::*; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->import_item.is_wildcard);
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
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kImportDecl) import_count++;
  }
  EXPECT_GE(import_count, 2);
}

// --- package_export_declaration ---
// export *::* ;
// | export package_import_item { , package_import_item } ;

TEST(ParserA213, PackageExportWildcard) {
  auto r = Parse(
      "package pkg;\n"
      "  export *::*;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->packages[0]->items.size(), 1u);
  auto* item = r.cu->packages[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(item->import_item.package_name, "*");
}

TEST(ParserA213, PackageExportSingleItem) {
  auto r = Parse(
      "package pkg;\n"
      "  export other_pkg::some_func;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->packages[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(item->import_item.package_name, "other_pkg");
  EXPECT_EQ(item->import_item.item_name, "some_func");
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
  for (auto* item : r.cu->packages[0]->items) {
    if (item->kind == ModuleItemKind::kExportDecl) export_count++;
  }
  EXPECT_GE(export_count, 2);
}

// --- package_import_item ---
// package_identifier :: identifier
// | package_identifier :: *

TEST(ParserA213, PackageImportItemNamed) {
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

TEST(ParserA213, PackageImportItemStar) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::*; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->import_item.package_name, "pkg");
  EXPECT_TRUE(item->import_item.is_wildcard);
}

// --- genvar_declaration ---
// genvar list_of_genvar_identifiers ;

TEST(ParserA213, GenvarDeclSingle) {
  auto r = Parse("module m; genvar i; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "i");
}

TEST(ParserA213, GenvarDeclMultiple) {
  auto r = Parse("module m; genvar i, j, k; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
}

// --- net_declaration ---
// Form 1: net_type [strength] [vectored|scalared] data_type_or_implicit
//          [delay3] list_of_net_decl_assignments ;
// Form 2: nettype_identifier [delay_control] list_of_net_decl_assignments ;
// Form 3: interconnect implicit_data_type [#delay]
//          net_identifier {unpacked_dim} [, ...] ;

TEST(ParserA213, NetDeclWireBasic) {
  auto r = Parse("module m; wire [7:0] data; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
}

TEST(ParserA213, NetDeclWithDriveStrength) {
  auto r = Parse("module m; wire (strong0, weak1) w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->drive_strength0, 0);
}

TEST(ParserA213, NetDeclTriregChargeStrength) {
  auto r = Parse("module m; trireg (medium) net1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA213, NetDeclVectored) {
  auto r = Parse("module m; wire vectored [7:0] bus; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA213, NetDeclScalared) {
  auto r = Parse("module m; wire scalared [7:0] bus; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA213, NetDeclWithDelay) {
  auto r = Parse("module m; wire #5 w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->net_delay, nullptr);
}

TEST(ParserA213, NetDeclMultipleAssign) {
  auto r = Parse("module m; wire a, b, c; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_GE(count, 3);
}

TEST(ParserA213, NetDeclInterconnect) {
  auto r = Parse("module m; interconnect net1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->data_type.is_interconnect);
}

// --- type_declaration ---
// Form 1: typedef data_type type_identifier { variable_dimension } ;
// Form 2: typedef ifc_port[sel].type_id type_id ; (not implemented — rare)
// Form 3: typedef [ forward_type ] type_identifier ;

TEST(ParserA213, TypedefBasic) {
  auto r = Parse("module m; typedef logic [7:0] byte_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "byte_t");
}

TEST(ParserA213, TypedefWithDims) {
  auto r = Parse("module m; typedef int arr_t [4]; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(ParserA213, TypedefEnum) {
  auto r = Parse("module m; typedef enum {A, B, C} abc_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kEnum);
}

TEST(ParserA213, TypedefStruct) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kStruct);
}

// --- forward_type ---
// enum | struct | union | class | interface class

TEST(ParserA213, ForwardTypedefClass) {
  auto r = Parse("module m; typedef class my_class; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "my_class");
}

TEST(ParserA213, ForwardTypedefInterfaceClass) {
  auto r = Parse("module m; typedef interface class my_ifc; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->name, "my_ifc");
}

TEST(ParserA213, ForwardTypedefEnum) {
  // forward_type: enum
  auto r = Parse("module m; typedef enum color_e; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "color_e");
}

TEST(ParserA213, ForwardTypedefStruct) {
  // forward_type: struct
  auto r = Parse("module m; typedef struct my_struct; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "my_struct");
}

TEST(ParserA213, ForwardTypedefUnion) {
  // forward_type: union
  auto r = Parse("module m; typedef union my_union; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "my_union");
}

// --- nettype_declaration ---
// Form 1: nettype data_type nettype_id [with [scope] tf_id] ;
// Form 2: nettype [scope] nettype_id nettype_id ;

TEST(ParserA213, NettypeDeclBasic) {
  auto r = Parse("module m; nettype real my_real_net; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->name, "my_real_net");
}

TEST(ParserA213, NettypeDeclWithResolve) {
  auto r = Parse("module m; nettype logic my_net with my_resolve; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->nettype_resolve_func, "my_resolve");
}

TEST(ParserA213, NettypeDeclWithScopedResolve) {
  // with package_scope tf_identifier
  auto r =
      Parse("module m; nettype logic my_net with pkg::resolve_fn; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->nettype_resolve_func, "resolve_fn");
}

// --- lifetime ---
// static | automatic

TEST(ParserA213, LifetimeStaticInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    static int x;\n"
      "  end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA213, LifetimeAutomaticInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int y;\n"
      "  end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA213, LifetimeInFunction) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int calc; return 0; endfunction\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_automatic);
}
