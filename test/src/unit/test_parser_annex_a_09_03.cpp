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

TEST(ParserA93, SimpleIdentInExpr) {
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

TEST(ParserA93, PackageScopeAccess) {
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

TEST(ParserA93, DpiImportWithCIdentifier) {
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

TEST(ParserA93, ModuleIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc("module my_module; endmodule\n", f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(cu->modules[0]->name, "my_module");
}

TEST(ParserA93, FunctionIdentifier) {
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
  ParseFixture f;
  auto* cu = ParseSrc("module \\my-module ; endmodule\n", f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA93, SystemCallInExpr) {
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

}
