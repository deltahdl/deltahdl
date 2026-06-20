#include "fixture_elaborator.h"

namespace {

TEST(NameSpaceElaboration, DistinctNamesInModuleScope) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a;\n"
             "  logic b;\n"
             "  wire c;\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, SameNameDifferentModulesElab) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
                         "module a; logic data; endmodule\n"
                         "module b; logic data; endmodule\n");
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  auto* cu = parser.Parse();
  ASSERT_FALSE(diag.HasErrors());

  Elaborator elab_a(arena, diag, cu);
  elab_a.Elaborate("a");
  EXPECT_FALSE(diag.HasErrors());
  Elaborator elab_b(arena, diag, cu);
  elab_b.Elaborate("b");
  EXPECT_FALSE(diag.HasErrors());
}

TEST(NameSpaceElaboration, DuplicateModuleDefinition) {
  EXPECT_FALSE(
      ElabOk("module m; endmodule\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, ModuleAndInterfaceSameName) {
  ElabFixture f;
  ElaborateSrc(
      "module foo; endmodule\n"
      "interface foo; endinterface\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(NameSpaceElaboration, ModuleAndProgramSameName) {
  ElabFixture f;
  ElaborateSrc(
      "module bar; endmodule\n"
      "program bar; endprogram\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(NameSpaceElaboration, DuplicatePackageDefinition) {
  EXPECT_FALSE(
      ElabOk("package p; endpackage\n"
             "package p; endpackage\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, DuplicateUdpDefinition) {
  EXPECT_FALSE(
      ElabOk("primitive p(output y, input a);\n"
             "  table 0 : 1 ; 1 : 0 ; endtable\n"
             "endprimitive\n"
             "primitive p(output y, input a);\n"
             "  table 0 : 1 ; 1 : 0 ; endtable\n"
             "endprimitive\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, DistinctDefinitionNamesOk) {
  EXPECT_TRUE(
      ElabOk("module m; endmodule\n"
             "interface ifc; endinterface\n"
             "program p; endprogram\n"));
}

TEST(NameSpaceElaboration, ModuleNameSpaceCoexist) {
  EXPECT_TRUE(
      ElabOk("module sub; endmodule\n"
             "module m;\n"
             "  parameter P = 1;\n"
             "  logic data;\n"
             "  wire net;\n"
             "  sub u0();\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, DuplicateCuScopeTypedef) {
  EXPECT_FALSE(
      ElabOk("typedef int foo;\n"
             "typedef int foo;\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, DuplicateCuScopeFunction) {
  EXPECT_FALSE(
      ElabOk("function int helper(int x); return x; endfunction\n"
             "function int helper(int x); return x + 1; endfunction\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, CuScopeTypedefAndVarSameName) {
  EXPECT_FALSE(
      ElabOk("typedef int foo;\n"
             "int foo;\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, CuScopeClassAndCuItemSameName) {
  EXPECT_FALSE(
      ElabOk("class foo; endclass\n"
             "int foo;\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, DuplicateCheckerAtCuScope) {
  EXPECT_FALSE(
      ElabOk("checker chk; endchecker\n"
             "checker chk; endchecker\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, CheckerAndCuItemSameName) {
  EXPECT_FALSE(
      ElabOk("checker foo; endchecker\n"
             "int foo;\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, ModuleAndCheckerSameNameOk) {
  EXPECT_TRUE(
      ElabOk("checker foo; endchecker\n"
             "module foo; endmodule\n"));
}

TEST(NameSpaceElaboration, RedeclVarInModuleScope) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic x;\n"
             "  logic x;\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, RedeclarationOfVariableAsNetError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  reg v;\n"
      "  wire v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(NameSpaceElaboration, RedeclarationOfNetAsVariableError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  wire w;\n"
      "  logic w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(NameSpaceElaboration, TaskSameNameAsVariableError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic foo;\n"
             "  task foo; endtask\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, TaskSameNameAsVariableInInterfaceError) {
  EXPECT_FALSE(
      ElabOk("interface i;\n"
             "  logic foo;\n"
             "  task foo; endtask\n"
             "endinterface\n"
             "module m;\n"
             "  i inst();\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, GateInstanceSameNameAsOutputNetError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  wire a, b;\n"
             "  wire g;\n"
             "  and g(g, a, b);\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, NamedBlockSameNameAsVariableError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic blk;\n"
             "  initial begin : blk\n"
             "    int y;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, ModuleInstanceSameNameAsVariableError) {
  EXPECT_FALSE(
      ElabOk("module child; endmodule\n"
             "module top;\n"
             "  logic u;\n"
             "  child u();\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, BlockNameSpaceDuplicateDeclarationError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  for (genvar i = 0; i < 2; i = i + 1) begin : g\n"
             "    logic x;\n"
             "    wire x;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, PortReintroducedAsVariableElaboratesOk) {
  EXPECT_TRUE(
      ElabOk("module m(data);\n"
             "  input data;\n"
             "  logic data;\n"
             "endmodule\n"));
}

}  // namespace
