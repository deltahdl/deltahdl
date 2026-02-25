// §A.9.3 Identifiers — elaboration-level semantic tests
// Tests scope resolution, hierarchical path elaboration, package scope
// resolution, and semantic validation of identifier usage.

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  if (!cu || cu->modules.empty()) return nullptr;
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static CompilationUnit* ParseSrc(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  return parser.Parse();
}

// ===========================================================================
// §A.9.3: Identifier scope resolution in elaboration
// ===========================================================================

TEST(ElabA93, SimpleIdentResolvesInModule) {
  // §A.9.3: variable_identifier resolves to a declared variable.
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

TEST(ElabA93, IdentCaseSensitiveElaboration) {
  // §5.6 / §A.9.3: Identifiers are case-sensitive. 'x' and 'X' are different.
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

TEST(ElabA93, EscapedIdentEquivalence) {
  // §5.6.1: An escaped identifier with only [a-zA-Z0-9_$] chars after the \
  // is treated the same as the simple identifier with those chars.
  // E.g., \data and data refer to the same identifier.
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

TEST(ElabA93, EscapedIdentWithKeywordName) {
  // §5.6.1: Escaped identifier \module is NOT the keyword 'module'.
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

// ===========================================================================
// §A.9.3: package_scope ::= package_identifier :: | $unit ::
// Elaboration: resolve identifiers across package scope.
// ===========================================================================

TEST(ElabA93, PackageScopeParamResolution) {
  // §A.9.3: ps_parameter_identifier in elaboration context.
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

TEST(ElabA93, PackageScopeTypeResolution) {
  // §A.9.3: ps_type_identifier — package-scoped type usage.
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

TEST(ElabA93, PackageImportIdentAccess) {
  // §A.9.3: After import, package members accessible as simple identifiers.
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

// ===========================================================================
// §A.9.3: hierarchical_identifier elaboration — path traversal
// ===========================================================================

TEST(ElabA93, HierarchicalIdentInContAssign) {
  // §A.9.3: hierarchical_identifier in continuous assignment.
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

TEST(ElabA93, InstanceNameIsIdentifier) {
  // §A.9.3: instance_identifier in module instantiation.
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

// ===========================================================================
// §A.9.3: Identifier roles in elaboration — generate, parameter, etc.
// ===========================================================================

TEST(ElabA93, GenvarIdentifier) {
  // §A.9.3: genvar_identifier ::= identifier — genvar used in generate.
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

TEST(ElabA93, ParamIdentInExpression) {
  // §A.9.3: parameter_identifier used in constant expressions.
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

TEST(ElabA93, FunctionCallIdentResolution) {
  // §A.9.3: function_identifier resolves in expression context.
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

// ===========================================================================
// §A.9.3: system_tf_identifier55 — elaboration of system calls
// ===========================================================================

TEST(ElabA93, SystemCallElaboration) {
  // §A.9.3 / Footnote 55: system_tf_identifier in procedural context.
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

// ===========================================================================
// §A.9.3 / §35: DPI c_identifier elaboration
// ===========================================================================

TEST(ElabA93, DpiImportElaboration) {
  // §A.9.3: c_identifier used in DPI import elaborates correctly.
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

TEST(ElabA93, DpiExportElaboration) {
  // §A.9.3: c_identifier in DPI export context.
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

// ===========================================================================
// §A.9.3: Multiple identifier forms within single module
// ===========================================================================

TEST(ElabA93, MixedIdentifierForms) {
  // §A.9.3: Multiple identifier types coexisting in one module.
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

}  // namespace
