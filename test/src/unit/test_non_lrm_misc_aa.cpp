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

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

RtlirDesign* Elaborate(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

namespace {

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

TEST(ParserA212, InoutUnpackedDim) {
  auto r = Parse("module m(inout logic a [3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_FALSE(port.unpacked_dims.empty());
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

TEST(ParserA212, OutputUnpackedDim) {
  auto r = Parse("module m(output logic q [1:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ParserA212, RefUnpackedDim) {
  auto r = Parse("module m(ref int arr [4]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kRef);
  EXPECT_FALSE(port.unpacked_dims.empty());
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

TEST(ParserA213, TypedefWithDims) {
  auto r = Parse("module m; typedef int arr_t [4]; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
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
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kStruct);
}

TEST(ParserA221, EnumNameWithRangeColon) {
  // enum_id [ integral_number : integral_number ]
  auto r = Parse("module m; enum {A[0:3] = 10} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& member = r.cu->modules[0]->items[0]->data_type.enum_members[0];
  EXPECT_NE(member.range_start, nullptr);
  EXPECT_NE(member.range_end, nullptr);
  EXPECT_NE(member.value, nullptr);
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
  auto* item = r.cu->modules[0]->items[0];
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
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
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
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
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
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
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
  auto& members = r.cu->modules[0]->items[0]->data_type.struct_members;
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
  auto* item = r.cu->modules[0]->items[0];
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
  for (auto* item : r.cu->modules[0]->items) {
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
  auto* item = r.cu->modules[0]->items[0];
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
  auto* item = r.cu->modules[0]->items[0];
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
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) count++;
  }
  EXPECT_GE(count, 3);
}

TEST(ParserA23, ListOfVariableDeclAssignmentsWithDims) {
  auto r = Parse("module m; logic [7:0] mem [256], cache [64]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
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
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_EQ(item->init_expr, nullptr);  // No initializer
}

TEST(ParserA24, NetDeclAssignmentWithUnpackedDims) {
  auto r = Parse("module m; wire w [3:0][7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

TEST(ParserA24, NetDeclAssignmentDimsAndInit) {
  auto r = Parse("module m; wire [7:0] mem [0:3] = '{0,1,2,3}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
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
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "WIDTH");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserA24, ParamAssignmentWithUnpackedDim) {
  auto r = Parse("module m; parameter int ARR [3:0] = '{1,2,3,4}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "ARR");
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

TEST(ParserA25, UnsizedDimWithInitInferSize) {
  ElabFixture f;
  auto* design = Elaborate("module m; int d [] = '{1,2,3}; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
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
  auto* item = r.cu->modules[0]->items[0];
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
  auto* item = r.cu->modules[0]->items[0];
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
  auto* item = r.cu->modules[0]->items[0];
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
  auto* item = r.cu->modules[0]->items[0];
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
  auto* item = r.cu->modules[0]->items[0];
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
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
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
  auto* mp = r.cu->interfaces[0]->modports[0];
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
  auto* mp = r.cu->interfaces[0]->modports[0];
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
  auto* mp = r.cu->interfaces[0]->modports[0];
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
  auto* mp = r.cu->interfaces[0]->modports[0];
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
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 4u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kOutput);
  EXPECT_TRUE(mp->ports[2].is_import);
  EXPECT_TRUE(mp->ports[3].is_export);
}

}  // namespace
