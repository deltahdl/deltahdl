// §A.9.3 Identifiers — parser-level tests
// Tests hierarchical_identifier, package_scope, ps_* identifier forms,
// and c_identifier in DPI context.

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static CompilationUnit* ParseSrc(const std::string& src, ParseFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  return parser.Parse();
}

// ===========================================================================
// §A.9.3: hierarchical_identifier ::= [ $root . ] { identifier
// constant_bit_select . } identifier
// ===========================================================================

TEST(ParserA93, SimpleIdentInExpr) {
  // §A.9.3: A single identifier in expression context.
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic x, y;\n"
      "  assign x = y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, HierarchicalIdentDotted) {
  // §A.9.3: hierarchical_identifier with multiple dot-separated identifiers.
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = sub_inst.data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, HierarchicalIdentDeep) {
  // §A.9.3: Deeply nested hierarchical path.
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = a.b.c.d.e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, HierarchicalIdentWithBitSelect) {
  // §A.9.3: { identifier constant_bit_select . } identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = inst_array[2].data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, HierarchicalIdentWithMultipleBitSelects) {
  // §A.9.3: Multiple path elements with bit selects.
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = top[0].mid[1].leaf;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, EscapedIdentInHierPath) {
  // §A.9.3: identifier ::= simple_identifier | escaped_identifier
  // Escaped identifiers are valid in hierarchical paths.
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = \\inst .data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// ===========================================================================
// §A.9.3: package_scope ::= package_identifier :: | $unit ::
// ===========================================================================

TEST(ParserA93, PackageScopeAccess) {
  // §A.9.3: package_identifier :: member
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n"
      "module m;\n"
      "  logic [pkg::WIDTH-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, PackageScopeOnType) {
  // §A.9.3: ps_type_identifier with package_scope.
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m;\n"
      "  pkg::byte_t data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, PackageScopeInAssign) {
  // §A.9.3: package_scope in expression within continuous assignment.
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n"
      "module m;\n"
      "  logic [pkg::WIDTH-1:0] data;\n"
      "  logic [pkg::WIDTH-1:0] result;\n"
      "  assign result = data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// ===========================================================================
// §A.9.3: c_identifier in DPI context (§35)
// c_identifier54 ::= [ a-zA-Z_ ] { [ a-zA-Z0-9_ ] }  (no $ allowed)
// ===========================================================================

TEST(ParserA93, DpiImportWithCIdentifier) {
  // §A.9.3 / §35: import "DPI-C" c_identifier = function ...
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  import \"DPI-C\" my_c_func = function void sv_func();\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* item = cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(item->dpi_c_name, "my_c_func");
  EXPECT_EQ(item->name, "sv_func");
}

TEST(ParserA93, DpiImportWithoutCIdentifier) {
  // §A.9.3 / §35: c_identifier is optional in DPI import.
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  import \"DPI-C\" function void my_func();\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* item = cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiImport);
  EXPECT_TRUE(item->dpi_c_name.empty());
  EXPECT_EQ(item->name, "my_func");
}

TEST(ParserA93, DpiExportWithCIdentifier) {
  // §A.9.3 / §35: export "DPI-C" c_identifier = function tf_identifier;
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  function void my_func(); endfunction\n"
      "  export \"DPI-C\" c_func_name = function my_func;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, DpiImportPureFunction) {
  // §A.9.3 / §35: import "DPI-C" pure function ...
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  import \"DPI-C\" pure function int compute(input int a, input int "
      "b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* item = cu->modules[0]->items[0];
  EXPECT_TRUE(item->dpi_is_pure);
}

TEST(ParserA93, DpiImportContextTask) {
  // §A.9.3 / §35: import "DPI-C" context task ...
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  import \"DPI-C\" context task my_task();\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* item = cu->modules[0]->items[0];
  EXPECT_TRUE(item->dpi_is_context);
  EXPECT_TRUE(item->dpi_is_task);
}

// ===========================================================================
// §A.9.3: Named identifier aliases used as different syntactic roles
// Tests that identifiers parse correctly in various declaration contexts.
// ===========================================================================

TEST(ParserA93, ModuleIdentifier) {
  // §A.9.3: module_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc("module my_module; endmodule\n", f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(cu->modules[0]->name, "my_module");
}

TEST(ParserA93, FunctionIdentifier) {
  // §A.9.3: function_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  function int my_func(int x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, TaskIdentifier) {
  // §A.9.3: task_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  task my_task; endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, ParameterIdentifier) {
  // §A.9.3: parameter_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, InstanceIdentifier) {
  // §A.9.3: instance_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "module sub; endmodule\n"
      "module m;\n"
      "  sub u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, GenerateBlockIdentifier) {
  // §A.9.3: generate_block_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 4; i = i + 1) begin : gen_blk\n"
      "      logic x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, InterfaceIdentifier) {
  // §A.9.3: interface_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "interface my_intf;\n"
      "  logic data;\n"
      "endinterface\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, PackageIdentifier) {
  // §A.9.3: package_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "package my_pkg;\n"
      "  parameter int X = 1;\n"
      "endpackage\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(cu->packages[0]->name, "my_pkg");
}

TEST(ParserA93, NetIdentifier) {
  // §A.9.3: net_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  wire my_net;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, VariableIdentifier) {
  // §A.9.3: variable_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic my_var;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, PortIdentifier) {
  // §A.9.3: port_identifier, input_port_identifier, output_port_identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m(input a, output b, inout c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(cu->modules[0]->ports.size(), 3u);
}

TEST(ParserA93, EnumIdentifier) {
  // §A.9.3: enum_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t my_color;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, ClassIdentifier) {
  // §A.9.3: class_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "class my_class;\n"
      "  int x;\n"
      "endclass\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, MemberIdentifier) {
  // §A.9.3: member_identifier ::= identifier (struct member)
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] field_a;\n"
      "    logic [7:0] field_b;\n"
      "  } my_struct_t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, SpecparamIdentifier) {
  // §A.9.3: specparam_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m(input a, output b);\n"
      "  specify\n"
      "    specparam tpd = 1.5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, GotoBlockLabel) {
  // §A.9.3: block_identifier ::= identifier (used as a label on begin/end)
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  initial begin : my_block\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, ConfigIdentifier) {
  // §A.9.3: config_identifier ::= identifier
  ParseFixture f;
  auto* cu = ParseSrc(
      "config my_cfg;\n"
      "  design top;\n"
      "endconfig\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, EscapedIdentAsModuleName) {
  // §A.9.3: identifier ::= simple_identifier | escaped_identifier.
  // Escaped identifiers valid in all identifier roles.
  ParseFixture f;
  auto* cu = ParseSrc("module \\my-module ; endmodule\n", f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// ===========================================================================
// §A.9.3: system_tf_identifier in expression and statement contexts
// ===========================================================================

TEST(ParserA93, SystemCallInExpr) {
  // §A.9.3: system_tf_identifier55 used in function call context.
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, SystemCallClog2) {
  // §A.9.3: system_tf_identifier with numeric suffix.
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  parameter int N = 8;\n"
      "  logic [$clog2(N)-1:0] addr;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
