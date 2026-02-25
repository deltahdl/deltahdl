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

namespace {


TEST(ParserSection22, FileAndLineInErrorMessage) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"Error at %s, line %d.\",\n"
              "    `__FILE__, `__LINE__);\n"
              "endmodule\n"));
}

TEST(ParserSection22, LineDirectiveInAssignment) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer line_num;\n"
              "  initial line_num = `__LINE__;\n"
              "endmodule\n"));
}

TEST(ParserSection22, FileDirectiveInStringConcat) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"source: %s:%0d\", `__FILE__, `__LINE__);\n"
              "endmodule\n"));
}

struct ParseResult2214 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult2214 Parse(const std::string& src) {
  ParseResult2214 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// ============================================================================
// LRM section 22.14 -- `begin_keywords, `end_keywords
// ============================================================================
TEST(ParserSection22, BeginKeywords1800_2023) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2023\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1800_2017) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2017\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1800_2012) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2012\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1800_2009) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2009\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1800_2005) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2005\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1364_2005) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1364-2005\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1364_2001) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1364-2001\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1364_2001_noconfig) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1364-2001-noconfig\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywords1364_1995) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1364-1995\"\n"
              "module t;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywordsWithModuleContent) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2017\"\n"
              "module t;\n"
              "  logic [7:0] data;\n"
              "  initial data = 8'hFF;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, BeginKeywordsMultipleModules) {
  EXPECT_TRUE(
      ParseOk("`begin_keywords \"1800-2012\"\n"
              "module m1;\n"
              "endmodule\n"
              "module m2;\n"
              "endmodule\n"
              "`end_keywords\n"));
}

TEST(ParserSection22, ModuleWithoutBeginKeywords) {
  auto r = Parse(
      "module m1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m1");
}

// ============================================================================
// AST-level checks for `begin_keywords
// ============================================================================
TEST(ParserSection22, BeginKeywordsModuleNamePreserved) {
  auto r = Parse(
      "`begin_keywords \"1800-2017\"\n"
      "module bar;\n"
      "  logic x;\n"
      "endmodule\n"
      "`end_keywords\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "bar");
}

// extern_tf_declaration inside a module (interface_or_generate_item applies
// to modules too via module_or_generate_item).
TEST(SourceText, ExternFunctionPrototypeInModule) {
  auto r = Parse(
      "module m;\n"
      "  extern function int compute(input int a, input int b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mod->items[0]->name, "compute");
  EXPECT_TRUE(mod->items[0]->is_extern);
  EXPECT_TRUE(mod->items[0]->func_body_stmts.empty());
}

// =============================================================================
// LRM §3.3 — Modules
// =============================================================================
// §3.3 Module with end label
TEST(ParserClause03, Cl3_3_ModuleEndLabel) {
  auto r = Parse(
      "module m;\n"
      "endmodule : m\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// §3.3 LRM mux2to1 example (verbatim, with always_comb procedural block).
TEST(ParserClause03, Cl3_3_Mux2to1LrmExample) {
  auto r = Parse(
      "module mux2to1 (input wire a, b, sel,\n"
      "                output logic y);\n"
      "  always_comb begin\n"
      "    if (sel) y = a;\n"
      "    else     y = b;\n"
      "  end\n"
      "endmodule: mux2to1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "mux2to1");
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[3].name, "y");
  auto* blk = FindItemByKind(r, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(blk, nullptr);
  EXPECT_EQ(blk->always_kind, AlwaysKind::kAlwaysComb);
}

// §3.3 Data declarations, constants, user-defined types, class definitions
TEST(ParserClause03, Cl3_3_ModuleDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] w;\n"
      "  logic [15:0] v;\n"
      "  struct packed { logic [3:0] a; logic [3:0] b; } s;\n"
      "  union packed { logic [7:0] x; logic [7:0] y; } u;\n"
      "  parameter WIDTH = 8;\n"
      "  localparam DEPTH = 16;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  class my_class; int val; endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kParamDecl));
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kTypedef));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kClassDecl));
  EXPECT_GE(r.cu->modules[0]->items.size(), 7u);
}

// §3.3 Subroutine definitions and procedural blocks
TEST(ParserClause03, Cl3_3_SubroutinesAndProceduralBlocks) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  task display_val(input int x); $display(\"%d\", x); endtask\n"
      "  initial a = 0;\n"
      "  final $display(\"done\");\n"
      "  always @(posedge clk) a <= b;\n"
      "  always_comb b = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kFunctionDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kTaskDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlways));
  EXPECT_TRUE(
      HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlwaysComb));
}

// 28. Port names as part of module scope
TEST(ParserClause03, Cl3_13_PortNamesInModuleScope) {
  auto r = Parse(
      "module m (input logic clk, input logic rst_n, output logic [7:0] q);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "rst_n");
  EXPECT_EQ(r.cu->modules[0]->ports[1].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "q");
  EXPECT_EQ(r.cu->modules[0]->ports[2].direction, Direction::kOutput);
}

// =============================================================================
// A.1.2 module_declaration — all forms
// =============================================================================
// module_keyword ::= module | macromodule
TEST(SourceText, ModuleKeywordMacromodule) {
  auto r = Parse("macromodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// =============================================================================
// A.1.2 description — all alternatives
// =============================================================================
// description: module_declaration
TEST(SourceText, DescriptionModule) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// Module with lifetime qualifier: module automatic m;
TEST(SourceText, ModuleWithLifetime) {
  auto r = Parse("module automatic m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// Module with end label: endmodule : m
TEST(SourceText, ModuleEndLabel) {
  auto r = Parse("module m; endmodule : m\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// =============================================================================
// A.1.2 module_declaration — wildcard port form: module m (.*);
// =============================================================================
TEST(SourceText, ModuleWildcardPorts) {
  auto r = Parse("module m(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->has_wildcard_ports);
}

// =============================================================================
// A.1.3 Module parameters and ports
// =============================================================================
// parameter_port_list ::= #( )
TEST(SourceText, EmptyParameterPortList) {
  auto r = Parse("module m #(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->params.empty());
}

// Module with both parameters and ports
TEST(SourceText, ParamsAndPorts) {
  auto r = Parse(
      "module m #(parameter int W = 8)(input logic [W-1:0] data,\n"
      "                                 output logic valid);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "W");
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "data");
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "valid");
}

// =============================================================================
// A.1 -- Source text productions
// =============================================================================
TEST(ParserAnnexA, A1ModuleDecl) {
  auto r = Parse("module m; endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

TEST(Parser, ModuleWithPorts) {
  auto r = Parse(
      "module mux(input logic a, input logic b, input logic sel, output logic "
      "y);\n"
      "  assign y = sel ? b : a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  struct Expected {
    Direction dir;
    const char* name;
  };
  Expected expected[] = {
      {Direction::kInput, "a"},
      {Direction::kInput, "b"},
      {Direction::kInput, "sel"},
      {Direction::kOutput, "y"},
  };
  ASSERT_EQ(mod->ports.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(mod->ports[i].direction, expected[i].dir) << "port " << i;
    EXPECT_EQ(mod->ports[i].name, expected[i].name) << "port " << i;
  }
}

// Module with non-ANSI header (list_of_ports).
TEST(SourceText, ModuleNonAnsiHeader) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

// Non-ANSI list_of_ports: port with multiple ports and body declarations
TEST(SourceText, NonAnsiMultiplePorts) {
  auto r = Parse(
      "module m(a, b, c);\n"
      "  input [7:0] a;\n"
      "  output [7:0] b;\n"
      "  inout c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 3u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[2].direction, Direction::kInout);
}

// Non-ANSI port_declaration with shared type: input [7:0] a, b;
TEST(SourceText, NonAnsiSharedType) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input [7:0] a, b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kInput);
}

TEST(ParserA212, InoutNonAnsi) {
  auto r = Parse("module m(a); inout wire [7:0] a; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
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

// --- list_of_interface_identifiers ---
// interface_identifier { unpacked_dimension }
//     { , interface_identifier { unpacked_dimension } }
// Note: Interface ports parse as non-ANSI when used without direction keyword.
// Multi-element interface port lists are resolved during semantic analysis.
TEST(ParserA23, ListOfInterfaceIdentifiersSingle) {
  auto r = Parse("module m(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
}

TEST(ParserA23, ListOfPortIdentifiersMultipleNonAnsi) {
  auto r = Parse("module m(a, b); input wire [7:0] a, b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  for (auto& port : r.cu->modules[0]->ports) {
    EXPECT_EQ(port.direction, Direction::kInput);
  }
}

// Module with ANSI header (list_of_port_declarations).
TEST(SourceText, ModuleAnsiHeader) {
  auto r = Parse("module m(input logic a, output logic b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

// port_declaration: all 4 directions (port_direction ::=
// input|output|inout|ref)
TEST(SourceText, PortDirectionAllFour) {
  auto r = Parse(
      "module m(input logic a, output logic b,\n"
      "         inout wire c, ref logic d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 4u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[2].direction, Direction::kInout);
  EXPECT_EQ(ports[3].direction, Direction::kRef);
}

// net_port_header: [port_direction] net_port_type — inout wire
TEST(SourceText, NetPortHeader) {
  auto r = Parse("module m(inout wire [7:0] data); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInout);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "data");
}

// variable_port_header: [port_direction] variable_port_type — input logic
TEST(SourceText, VariablePortHeader) {
  auto r = Parse("module m(input logic [3:0] sel); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "sel");
}

TEST(ParserAnnexA, A1ModulePortDirections) {
  auto r = Parse(
      "module m(input logic a, output logic b,\n"
      "         inout wire c, ref logic d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 4u);
  const Direction kExpected[] = {Direction::kInput, Direction::kOutput,
                                 Direction::kInout, Direction::kRef};
  for (size_t i = 0; i < 4; i++) {
    EXPECT_EQ(ports[i].direction, kExpected[i]);
  }
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

TEST(ParserA212, InoutPackedDim) {
  auto r = Parse("module m(inout [7:0] a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ParserA212, InputVariablePortTypeVar) {
  // variable_port_type ::= var_data_type
  // var_data_type ::= var data_type_or_implicit
  auto r = Parse("module m(input var logic d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
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

// --- ref_declaration ---
// ref variable_port_type list_of_variable_identifiers
TEST(ParserA212, RefDeclaration) {
  auto r = Parse("module m(ref logic [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kRef);
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

// --- list_of_port_identifiers ---
// port_identifier { unpacked_dimension }
//     { , port_identifier { unpacked_dimension } }
TEST(ParserA23, ListOfPortIdentifiersSingle) {
  auto r = Parse("module m(inout wire a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInout);
}

TEST(ParserA23, ListOfPortIdentifiersWithUnpackedDim) {
  auto r = Parse("module m(inout logic a [3:0]); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->ports[0].unpacked_dims.empty());
}

// --- list_of_variable_identifiers ---
// variable_identifier { variable_dimension }
//     { , variable_identifier { variable_dimension } }
TEST(ParserA23, ListOfVariableIdentifiersSingle) {
  auto r = Parse("module m(input logic d); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

TEST(ParserA23, ListOfVariableIdentifiersMultipleAnsi) {
  auto r = Parse(
      "module m(input logic a, input logic b, input logic c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  for (auto& port : r.cu->modules[0]->ports) {
    EXPECT_EQ(port.direction, Direction::kInput);
  }
}

TEST(ParserA23, ListOfVariableIdentifiersWithDim) {
  auto r = Parse("module m(input logic d [3:0]); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->ports[0].unpacked_dims.empty());
}

TEST(ParserA23, ListOfVariablePortIdentifiersMultipleAnsi) {
  auto r = Parse(
      "module m(output logic a = 1'b0, output logic b = 1'b1); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_NE(r.cu->modules[0]->ports[0].default_value, nullptr);
  EXPECT_NE(r.cu->modules[0]->ports[1].default_value, nullptr);
}

TEST(ParserA23, ListOfVariablePortIdentifiersWithDim) {
  auto r = Parse("module m(output logic q [1:0] = '{0, 0}); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_FALSE(port.unpacked_dims.empty());
  EXPECT_NE(port.default_value, nullptr);
}

TEST(ParserA25, PortWithPackedDim) {
  auto r = Parse("module m(input logic [15:0] data); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  ASSERT_NE(r.cu->modules[0]->ports[0].data_type.packed_dim_left, nullptr);
}

// ansi_port_declaration with default value: input logic a = 1'b0
TEST(SourceText, AnsiPortWithDefault) {
  auto r = Parse("module m(input logic a = 1'b0); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_NE(r.cu->modules[0]->ports[0].default_value, nullptr);
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

TEST(ParserSection23, MacromoduleDefinition) {
  auto r = Parse(
      "macromodule top;\n"
      "  wire a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "top");
}

TEST(Parser, EmptyModule) {
  auto r = Parse("module empty; endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "empty");
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

TEST(Parser, MultipleModules) {
  auto r = Parse(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 3);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

// §3.3 Design element instantiations
TEST(ParserClause03, Cl3_3_DesignElementInstantiations) {
  auto r = Parse(
      "module child; endmodule\n"
      "module top;\n"
      "  logic sig;\n"
      "  child c0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  // "top" is modules[1]; check it has the instantiation.
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst));
}

// Nested module_declaration as non_port_module_item.
TEST(SourceText, NestedModuleDeclaration) {
  auto r = Parse(
      "module outer;\n"
      "  module inner;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind,
            ModuleItemKind::kNestedModuleDecl);
  EXPECT_NE(r.cu->modules[0]->items[0]->nested_module_decl, nullptr);
  EXPECT_EQ(r.cu->modules[0]->items[0]->nested_module_decl->name, "inner");
}

// Extern module declaration.
TEST(SourceText, ExternModule) {
  auto r = Parse("extern module m(input logic a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
}

// 19. Hierarchical reference syntax (a.b.c)
TEST(ParserClause03, Cl3_13_HierarchicalReferenceSyntax) {
  // Hierarchical names like top.sub.sig are member-access expressions.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    $display(\"%0d\", top.sub.sig);\n"
              "  end\n"
              "endmodule\n"));
}

// --- Defparam tests ---
TEST(Parser, DefparamSingle) {
  auto r = Parse(
      "module top;\n"
      "  defparam u0.WIDTH = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  ASSERT_EQ(item->defparam_assigns.size(), 1);
  EXPECT_NE(item->defparam_assigns[0].first, nullptr);
  EXPECT_NE(item->defparam_assigns[0].second, nullptr);
}

TEST(Parser, DefparamMultiple) {
  auto r = Parse(
      "module top;\n"
      "  defparam u0.WIDTH = 8, u1.DEPTH = 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(item->defparam_assigns.size(), 2);
}

// parameter_override: defparam list_of_defparam_assignments.
TEST(SourceText, ParameterOverrideDefparam) {
  auto r = Parse(
      "module m;\n"
      "  defparam sub.W = 16, sub.D = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  auto* dp = r.cu->modules[0]->items[0];
  EXPECT_EQ(dp->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(dp->defparam_assigns.size(), 2u);
}

// =============================================================================
// A.2.3 Declaration lists
// =============================================================================
// --- list_of_defparam_assignments ---
// defparam_assignment { , defparam_assignment }
TEST(ParserA23, ListOfDefparamAssignmentsSingle) {
  auto r = Parse(
      "module top;\n"
      "  defparam u0.WIDTH = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(item->defparam_assigns.size(), 1u);
}

TEST(ParserA23, ListOfDefparamAssignmentsMultiple) {
  auto r = Parse(
      "module top;\n"
      "  defparam u0.WIDTH = 16, u1.DEPTH = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(item->defparam_assigns.size(), 2u);
}

// =============================================================================
// A.2.4 Declaration assignments
// =============================================================================
// --- defparam_assignment ---
// hierarchical_parameter_identifier = constant_mintypmax_expression
TEST(ParserA24, DefparamAssignmentHierarchical) {
  auto r = Parse(
      "module top;\n"
      "  defparam u0.sub.WIDTH = 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  ASSERT_EQ(item->defparam_assigns.size(), 1u);
  // The path expression should be a hierarchical reference
  EXPECT_NE(item->defparam_assigns[0].first, nullptr);
  EXPECT_NE(item->defparam_assigns[0].second, nullptr);
}

TEST(ParserA24, DefparamAssignmentMintypmax) {
  // constant_mintypmax_expression: expr : expr : expr
  auto r = Parse(
      "module top;\n"
      "  defparam u0.DELAY = 1:2:3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  ASSERT_EQ(item->defparam_assigns.size(), 1u);
}

// =============================================================================
// A.1.2 bind_directive (§23.11)
// =============================================================================
// Form 1: bind target_scope bind_instantiation
TEST(SourceText, BindDirectiveBasic) {
  auto r = Parse("bind target_mod checker_mod chk_inst(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "target_mod");
  EXPECT_TRUE(r.cu->bind_directives[0]->target_instances.empty());
  ASSERT_NE(r.cu->bind_directives[0]->instantiation, nullptr);
  EXPECT_EQ(r.cu->bind_directives[0]->instantiation->inst_module,
            "checker_mod");
  EXPECT_EQ(r.cu->bind_directives[0]->instantiation->inst_name, "chk_inst");
}

// Form 1 with instance list: bind scope : inst1, inst2 instantiation
TEST(SourceText, BindDirectiveWithInstanceList) {
  auto r = Parse("bind dut : i1, i2 chk chk_i(.clk(clk));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "dut");
  ASSERT_EQ(r.cu->bind_directives[0]->target_instances.size(), 2u);
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[0], "i1");
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[1], "i2");
}

// Form 2: bind hierarchical_instance instantiation
TEST(SourceText, BindDirectiveHierarchical) {
  auto r = Parse("bind top.dut.u1 checker_mod chk(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "top.dut.u1");
}

}  // namespace
