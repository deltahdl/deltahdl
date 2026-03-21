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

TEST(IdentifierSyntaxParsing, SimpleIdentInExpr) {
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

TEST(IdentifierSyntaxParsing, HierarchicalIdentDotted) {
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

TEST(IdentifierSyntaxParsing, HierarchicalIdentDeep) {
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

TEST(IdentifierSyntaxParsing, HierarchicalIdentWithBitSelect) {
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

TEST(IdentifierSyntaxParsing, HierarchicalIdentWithMultipleBitSelects) {
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

TEST(IdentifierSyntaxParsing, EscapedIdentInHierPath) {
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

TEST(IdentifierSyntaxParsing, PackageScopeAccess) {
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

TEST(IdentifierSyntaxParsing, PackageScopeOnType) {
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

TEST(IdentifierSyntaxParsing, PackageScopeInAssign) {
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

TEST(IdentifierSyntaxParsing, DpiImportWithCIdentifier) {
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

TEST(IdentifierSyntaxParsing, DpiImportWithoutCIdentifier) {
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

TEST(IdentifierSyntaxParsing, DpiExportWithCIdentifier) {
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

TEST(IdentifierSyntaxParsing, DpiImportPureFunction) {
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

TEST(IdentifierSyntaxParsing, DpiImportContextTask) {
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

TEST(IdentifierSyntaxParsing, ModuleIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc("module my_module; endmodule\n", f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(cu->modules[0]->name, "my_module");
}

TEST(IdentifierSyntaxParsing, FunctionIdentifier) {
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

TEST(IdentifierSyntaxParsing, TaskIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  task my_task; endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, ParameterIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, InstanceIdentifier) {
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

TEST(IdentifierSyntaxParsing, GenerateBlockIdentifier) {
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

TEST(IdentifierSyntaxParsing, InterfaceIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "interface my_intf;\n"
      "  logic data;\n"
      "endinterface\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PackageIdentifier) {
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

TEST(IdentifierSyntaxParsing, NetIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  wire my_net;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, VariableIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic my_var;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PortIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m(input a, output b, inout c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(cu->modules[0]->ports.size(), 3u);
}

TEST(IdentifierSyntaxParsing, EnumIdentifier) {
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

TEST(IdentifierSyntaxParsing, ClassIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "class my_class;\n"
      "  int x;\n"
      "endclass\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, MemberIdentifier) {
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

TEST(IdentifierSyntaxParsing, SpecparamIdentifier) {
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

TEST(IdentifierSyntaxParsing, GotoBlockLabel) {
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

TEST(IdentifierSyntaxParsing, ConfigIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "config my_cfg;\n"
      "  design top;\n"
      "endconfig\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, EscapedIdentAsModuleName) {
  ParseFixture f;
  auto* cu = ParseSrc("module \\my-module ; endmodule\n", f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, SystemCallInExpr) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, SystemCallClog2) {
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

TEST(IdentifierSyntaxParsing, UnitScopePackageAccess) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = $unit::top_param;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, SystemIdentNoArgsAsStatement) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  initial $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, SystemIdentMultipleInBlock) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  initial begin\n"
      "    $display(\"a\");\n"
      "    $write(\"b\");\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, EscapedIdentInPackageScope) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package \\my-pkg ;\n"
      "  parameter int W = 4;\n"
      "endpackage\n"
      "module m;\n"
      "  logic [\\my-pkg ::W-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, TypeIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  typedef logic [7:0] my_type_t;\n"
      "  my_type_t data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, ProgramIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "program my_prog;\n"
      "  initial $finish;\n"
      "endprogram\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, GenvarIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  genvar i;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, CovergroupIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "class my_class;\n"
      "  int val;\n"
      "  covergroup cg;\n"
      "    coverpoint val;\n"
      "  endgroup\n"
      "endclass\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PropertyIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m(input clk, input a);\n"
      "  property my_prop;\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, SequenceIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m(input clk, input a, input b);\n"
      "  sequence my_seq;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
