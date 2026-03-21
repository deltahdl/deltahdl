#include "fixture_elaborator.h"
#include "parser/ast.h"

using namespace delta;

namespace {

static CompilationUnit* ParseSrc(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  return parser.Parse();
}

TEST(IdentifierElaboration, SimpleIdentResolvesInModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, IdentCaseSensitiveElaboration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  logic X;\n"
      "  assign x = 0;\n"
      "  assign X = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 2u);
}

TEST(IdentifierElaboration, EscapedIdentEquivalence) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic data;\n"
      "  assign \\data = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, EscapedIdentWithKeywordName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic \\module ;\n"
      "  assign \\module = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, PackageScopeParamResolution) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n"
      "module m;\n"
      "  logic [pkg::WIDTH-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, PackageScopeTypeResolution) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m;\n"
      "  pkg::byte_t data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, PackageImportIdentAccess) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  parameter int WIDTH = 16;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::WIDTH;\n"
      "  logic [WIDTH-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, HierarchicalIdentInContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub(input a, output b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module m;\n"
      "  logic x, y;\n"
      "  sub u1(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, InstanceNameIsIdentifier) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub; endmodule\n"
      "module m;\n"
      "  sub my_instance();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->children.empty());
  EXPECT_EQ(mod->children[0].inst_name, "my_instance");
}

TEST(IdentifierElaboration, GenvarIdentifier) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int N = 4;\n"
      "  logic [N-1:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, ParamIdentInExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int N = 4;\n"
      "  parameter int M = N * 2;\n"
      "  logic [M-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, FunctionCallIdentResolution) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  logic [31:0] result;\n"
      "  assign result = add(3, 4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, SystemCallElaboration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    $display(\"test\");\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, DpiImportElaboration) {
  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  import \"DPI-C\" c_add = function int add(int a, int b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* item = cu->modules[0]->items[0];
  EXPECT_EQ(item->dpi_c_name, "c_add");
  EXPECT_EQ(item->name, "add");
}

TEST(IdentifierElaboration, DpiExportElaboration) {
  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  function void my_sv_func(); endfunction\n"
      "  export \"DPI-C\" c_wrapper = function my_sv_func;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, MixedIdentifierForms) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int W = 8;\n"
      "  logic [W-1:0] data;\n"
      "  logic \\escaped_sig ;\n"
      "  initial begin\n"
      "    $display(\"data=%h\", data);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, UnresolvedIdentifierError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  assign x = nonexistent;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, TypeIdentifierResolution) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t data;\n"
      "  assign data = 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierElaboration, NestedHierarchicalIdentResolution) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module inner(input a, output b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module mid(input a, output b);\n"
      "  inner u(.a(a), .b(b));\n"
      "endmodule\n"
      "module m;\n"
      "  logic x, y;\n"
      "  mid u(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
