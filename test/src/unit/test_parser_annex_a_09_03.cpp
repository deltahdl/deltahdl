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

TEST(IdentifierSyntaxParsing, HierarchicalIdentWithRoot) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = $root.top.signal;\n"
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

TEST(IdentifierSyntaxParsing, PackageScopeUnit) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "int cu_var = 0;\n"
      "module m;\n"
      "  int x;\n"
      "  initial x = $unit::cu_var;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PackageScopeNamed) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  int v = 0;\n"
      "endpackage\n"
      "module m;\n"
      "  int x;\n"
      "  initial x = pkg::v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, DpiImportCIdentifierWithDollarIsError) {
  ParseFixture f;
  ParseSrc(
      "module m;\n"
      "  import \"DPI-C\" bad$name = function void sv_func();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, DpiExportCIdentifierWithDollarIsError) {
  ParseFixture f;
  ParseSrc(
      "module m;\n"
      "  function void sv_func(); endfunction\n"
      "  export \"DPI-C\" bad$name = function sv_func;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, DpiImportCIdentifierLeadingDigitIsError) {
  ParseFixture f;
  ParseSrc(
      "module m;\n"
      "  import \"DPI-C\" 9bad = function void sv_func();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, SimpleIdentifierWithDollarInBody) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic my$var;\n"
      "  assign my$var = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsTypeIdentifierFromPackage) {
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

TEST(IdentifierSyntaxParsing, PsOrHierarchicalTfIdentifierPackageScopedCall) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  function int helper(int x); return x + 1; endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  int y;\n"
      "  initial y = pkg::helper(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, EscapedIdentifierInExpr) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic \\busy-signal ;\n"
      "  assign \\busy-signal = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsClassIdentifierFromPackage) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  class my_class;\n"
      "    int x;\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  pkg::my_class h;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsParameterIdentifierFromGenerateBlock) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 4; i = i + 1) begin : gen_blk\n"
      "      localparam int LOCAL_P = 1;\n"
      "    end\n"
      "  endgenerate\n"
      "  logic [gen_blk[0].LOCAL_P-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsOrHierarchicalNetIdentifierAcrossPackage) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  parameter int W = 8;\n"
      "endpackage\n"
      "module m;\n"
      "  logic [pkg::W-1:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, ModportIdentifierAfterDot) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "interface my_if;\n"
      "  logic d;\n"
      "  modport mp(input d);\n"
      "endinterface\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, NettypeIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  nettype real my_real_net;\n"
      "endpackage\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, SimpleIdentifierAllowsUnderscoreAndDigits) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m_1;\n"
      "  logic abc_2_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(cu->modules[0]->name, "m_1");
}

TEST(IdentifierSyntaxParsing, HierarchicalIdentifierTfCall) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module sub;\n"
      "  function int helper(); return 1; endfunction\n"
      "endmodule\n"
      "module m;\n"
      "  sub u();\n"
      "  int y;\n"
      "  initial y = u.helper();\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsOrHierarchicalPropertyIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module sub(input clk, input a);\n"
      "  property p_ok;\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n"
      "module m(input clk, input a);\n"
      "  sub u(.clk(clk), .a(a));\n"
      "  assert property (u.p_ok);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsOrHierarchicalSequenceIdentifier) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module sub(input clk, input a, input b);\n"
      "  sequence s_ab;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n"
      "module m(input clk, input a, input b);\n"
      "  sub u(.clk(clk), .a(a), .b(b));\n"
      "  cover property (u.s_ab);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, IndexVariableIdentifierInForeach) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  int data [4];\n"
      "  initial begin\n"
      "    foreach (data[idx]) data[idx] = idx;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, ConstraintIdentifierInClass) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "class c;\n"
      "  rand int x;\n"
      "  constraint c_range { x > 0; x < 10; }\n"
      "endclass\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_FALSE(cu->classes.empty());
  bool found = false;
  for (auto* m : cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == "c_range") {
      found = true;
      break;
    }
  }
  EXPECT_TRUE(found);
}

TEST(IdentifierSyntaxParsing, ClockingIdentifierInClockingBlock) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m(input clk, input d);\n"
      "  clocking cb @(posedge clk);\n"
      "    input d;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_FALSE(cu->modules.empty());
  bool found = false;
  for (auto* item : cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kClockingBlock && item->name == "cb") {
      found = true;
      break;
    }
  }
  EXPECT_TRUE(found);
}

TEST(IdentifierSyntaxParsing, UdpIdentifierInPrimitive) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "primitive my_buf (out, in);\n"
      "  output out;\n"
      "  input in;\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(cu->udps.size(), 1u);
  EXPECT_EQ(cu->udps[0]->name, "my_buf");
}

TEST(IdentifierSyntaxParsing, MethodIdentifierInClass) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "class c;\n"
      "  function int get_x();\n"
      "    return 7;\n"
      "  endfunction\n"
      "  task do_thing();\n"
      "  endtask\n"
      "endclass\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_FALSE(cu->classes.empty());
  bool saw_func = false;
  bool saw_task = false;
  for (auto* m : cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
      if (m->method->name == "get_x") saw_func = true;
      if (m->method->name == "do_thing") saw_task = true;
    }
  }
  EXPECT_TRUE(saw_func);
  EXPECT_TRUE(saw_task);
}

TEST(IdentifierSyntaxParsing, BlockIdentifierOnSequentialBlock) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  initial begin : init_blk\n"
      "    logic x;\n"
      "    x = 1'b0;\n"
      "  end : init_blk\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsIdentifierGenericFromPackage) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  int counter = 0;\n"
      "endpackage\n"
      "module m;\n"
      "  int y;\n"
      "  initial y = pkg::counter;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, TerminalIdentifierInUdpPort) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "primitive p_inv (q, a);\n"
      "  output q;\n"
      "  input a;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(cu->udps.size(), 1u);
  EXPECT_EQ(cu->udps[0]->output_name, "q");
  ASSERT_EQ(cu->udps[0]->input_names.size(), 1u);
  EXPECT_EQ(cu->udps[0]->input_names[0], "a");
}

TEST(IdentifierSyntaxParsing, InterfacePortIdentifierAsModulePort) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "interface my_if;\n"
      "  logic d;\n"
      "endinterface\n"
      "module m(my_if iface);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}


}  // namespace
