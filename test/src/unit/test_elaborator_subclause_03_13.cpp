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

TEST(NameSpaceElaboration, DistinctPackagesOk) {
  // §3.13(b): the package name space only forbids reusing a package name;
  // distinctly named packages coexist.
  EXPECT_TRUE(
      ElabOk("package p1; endpackage\n"
             "package p2; endpackage\n"
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

TEST(NameSpaceElaboration, ModuleAndPrimitiveSameName) {
  // §3.13(a): the definitions name space unifies module AND primitive
  // identifiers, so a UDP may not reuse a name already taken by a module.
  EXPECT_FALSE(
      ElabOk("module foo; endmodule\n"
             "primitive foo(output y, input a);\n"
             "  table 0 : 1 ; 1 : 0 ; endtable\n"
             "endprimitive\n"));
}

TEST(NameSpaceElaboration, DuplicateInterfaceDefinition) {
  // §3.13(a): interfaces share the single definitions name space, so an
  // interface name may not be reused for another interface.
  EXPECT_FALSE(
      ElabOk("interface ifc; endinterface\n"
             "interface ifc; endinterface\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, DuplicateProgramDefinition) {
  // §3.13(a): programs share the single definitions name space, so a program
  // name may not be reused for another program.
  EXPECT_FALSE(
      ElabOk("program pr; endprogram\n"
             "program pr; endprogram\n"
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

TEST(NameSpaceElaboration, DuplicateCuScopeTask) {
  // §3.13(c): tasks are unified in the compilation-unit scope name space.
  EXPECT_FALSE(
      ElabOk("task t; endtask\n"
             "task t; endtask\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, DuplicateCuScopeVariable) {
  // §3.13(c): variable declarations are unified in the compilation-unit scope.
  EXPECT_FALSE(
      ElabOk("int a;\n"
             "int a;\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, DuplicateCuScopeNet) {
  // §3.13(c): net declarations are unified in the compilation-unit scope.
  EXPECT_FALSE(
      ElabOk("wire w;\n"
             "wire w;\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, DuplicateCuScopeNamedEvent) {
  // §3.13(c): named events are unified in the compilation-unit scope.
  EXPECT_FALSE(
      ElabOk("event e;\n"
             "event e;\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, DuplicateCuScopeParameter) {
  // §3.13(c): parameters are unified in the compilation-unit scope name space.
  EXPECT_FALSE(
      ElabOk("localparam int P = 1;\n"
             "localparam int P = 2;\n"
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

TEST(NameSpaceElaboration, NamedEventSameNameAsVariableError) {
  // §3.13(e): named events are unified with variables in the module name space,
  // so an event may not share a name with a variable in the same module.
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  event e;\n"
             "  logic e;\n"
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

TEST(NameSpaceElaboration, DuplicateLocalInSameProceduralBlockError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    int x;\n"
             "    int x;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, SameLocalNameInNestedBlockOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    int x;\n"
             "    begin\n"
             "      int x;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, SameLocalNameInSiblingBlocksOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    begin\n"
             "      int x;\n"
             "    end\n"
             "    begin\n"
             "      int x;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, FunctionBodyDuplicateLocalError) {
  // §3.13(f): the function construct introduces a block name space, so a local
  // may not be redeclared by another local in the same function body.
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  function int f();\n"
             "    int x;\n"
             "    int x;\n"
             "    return 0;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, TaskBodyDuplicateLocalError) {
  // §3.13(f): the task construct likewise introduces a block name space.
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  task t();\n"
             "    int y;\n"
             "    int y;\n"
             "  endtask\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, SameLocalNameInFunctionNestedBlockOk) {
  // §3.13(f): a nested begin-end inside a function body is a distinct block
  // name space, so reusing the name there is legal shadowing, not a
  // redeclaration.
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int f();\n"
             "    int x;\n"
             "    begin\n"
             "      int x;\n"
             "    end\n"
             "    return 0;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, PortReintroducedAsVariableElaboratesOk) {
  EXPECT_TRUE(
      ElabOk("module m(data);\n"
             "  input data;\n"
             "  logic data;\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, PortReintroducedAsNetElaboratesOk) {
  // §3.13(g): a port name may be reintroduced in the module name space by a
  // variable OR a net declaration; here the net form is observed at
  // elaboration.
  EXPECT_TRUE(
      ElabOk("module m(data);\n"
             "  input data;\n"
             "  wire data;\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, AttributeNameCoincidesWithVariableElaboratesOk) {
  // §3.13(h): an attribute name (§5.12 real syntax `(* ... *)`) lives only in
  // the attribute name space and never enters the module name space, so it may
  // coincide with a variable name without a redeclaration error. Driven through
  // the full pipeline so the attribute is really parsed and elaborated.
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  (* keep *) logic keep;\n"
             "endmodule\n"));
}

}  // namespace
