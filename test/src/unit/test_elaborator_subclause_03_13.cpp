#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m; endmodule\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "duplicate definition of 'm'",
                            2, "3.13"));
}

TEST(NameSpaceElaboration, ModuleAndInterfaceSameName) {
  ElabFixture f;
  ElaborateSrc(
      "module foo; endmodule\n"
      "interface foo; endinterface\n",
      f);
  // The interface loop in elaborator_validate_config.cpp runs after the module
  // loop, so the interface is the later insertion and carries the report.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate definition of 'foo'", 2, "3.13"));
}

TEST(NameSpaceElaboration, ModuleAndProgramSameName) {
  ElabFixture f;
  ElaborateSrc(
      "module bar; endmodule\n"
      "program bar; endprogram\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate definition of 'bar'", 2, "3.13"));
}

TEST(NameSpaceElaboration, DuplicatePackageDefinition) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p; endpackage\n"
             "package p; endpackage\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "duplicate package 'p'", 2, "3.13"));
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
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("primitive p(output y, input a);\n"
             "  table 0 : 1 ; 1 : 0 ; endtable\n"
             "endprimitive\n"
             "primitive p(output y, input a);\n"
             "  table 0 : 1 ; 1 : 0 ; endtable\n"
             "endprimitive\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "duplicate definition of 'p'",
                            4, "3.13"));
}

TEST(NameSpaceElaboration, ModuleAndPrimitiveSameName) {
  // §3.13(a): the definitions name space unifies module AND primitive
  // identifiers, so a UDP may not reuse a name already taken by a module.
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module foo; endmodule\n"
             "primitive foo(output y, input a);\n"
             "  table 0 : 1 ; 1 : 0 ; endtable\n"
             "endprimitive\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate definition of 'foo'", 2, "3.13"));
}

TEST(NameSpaceElaboration, DuplicateInterfaceDefinition) {
  // §3.13(a): interfaces share the single definitions name space, so an
  // interface name may not be reused for another interface.
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("interface ifc; endinterface\n"
             "interface ifc; endinterface\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate definition of 'ifc'", 2, "3.13"));
}

TEST(NameSpaceElaboration, DuplicateProgramDefinition) {
  // §3.13(a): programs share the single definitions name space, so a program
  // name may not be reused for another program.
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("program pr; endprogram\n"
             "program pr; endprogram\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate definition of 'pr'", 2, "3.13"));
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
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("typedef int foo;\n"
             "typedef int foo;\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 'foo' in compilation-unit scope",
                            2, "3.13"));
}

TEST(NameSpaceElaboration, DuplicateCuScopeFunction) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("function int helper(int x); return x; endfunction\n"
             "function int helper(int x); return x + 1; endfunction\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "redeclaration of 'helper' in compilation-unit scope", 2, "3.13"));
}

TEST(NameSpaceElaboration, CuScopeTypedefAndVarSameName) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("typedef int foo;\n"
             "int foo;\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 'foo' in compilation-unit scope",
                            2, "3.13"));
}

TEST(NameSpaceElaboration, CuScopeClassAndCuItemSameName) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class foo; endclass\n"
             "int foo;\n"
             "module m; endmodule\n",
             f));
  // A class is held in CompilationUnit::classes, which
  // elaborator_validate_config.cpp walks after CompilationUnit::cu_items, so
  // the class is the later insertion and the report stands on line 1.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 'foo' in compilation-unit scope",
                            1, "3.13"));
}

TEST(NameSpaceElaboration, DuplicateCheckerAtCuScope) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("checker chk; endchecker\n"
             "checker chk; endchecker\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 'chk' in compilation-unit scope",
                            2, "3.13"));
}

TEST(NameSpaceElaboration, CheckerAndCuItemSameName) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("checker foo; endchecker\n"
             "int foo;\n"
             "module m; endmodule\n",
             f));
  // CompilationUnit::checkers is walked after CompilationUnit::cu_items, so the
  // checker is the later insertion and the report stands on line 1.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 'foo' in compilation-unit scope",
                            1, "3.13"));
}

TEST(NameSpaceElaboration, DuplicateCuScopeTask) {
  // §3.13(c): tasks are unified in the compilation-unit scope name space.
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("task t; endtask\n"
             "task t; endtask\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 't' in compilation-unit scope", 2,
                            "3.13"));
}

TEST(NameSpaceElaboration, DuplicateCuScopeVariable) {
  // §3.13(c): variable declarations are unified in the compilation-unit scope.
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("int a;\n"
             "int a;\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 'a' in compilation-unit scope", 2,
                            "3.13"));
}

TEST(NameSpaceElaboration, DuplicateCuScopeNet) {
  // §3.13(c): net declarations are unified in the compilation-unit scope.
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("wire w;\n"
             "wire w;\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 'w' in compilation-unit scope", 2,
                            "3.13"));
}

TEST(NameSpaceElaboration, DuplicateCuScopeNamedEvent) {
  // §3.13(c): named events are unified in the compilation-unit scope.
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("event e;\n"
             "event e;\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 'e' in compilation-unit scope", 2,
                            "3.13"));
}

TEST(NameSpaceElaboration, DuplicateCuScopeParameter) {
  // §3.13(c): parameters are unified in the compilation-unit scope name space.
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("localparam int P = 1;\n"
             "localparam int P = 2;\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 'P' in compilation-unit scope", 2,
                            "3.13"));
}

TEST(NameSpaceElaboration, ModuleAndCheckerSameNameOk) {
  EXPECT_TRUE(
      ElabOk("checker foo; endchecker\n"
             "module foo; endmodule\n"));
}

TEST(NameSpaceElaboration, RedeclVarInModuleScope) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic x;\n"
             "  logic x;\n"
             "endmodule\n",
             f));
  // The module name space is §23.9's, so that is the subclause the report
  // carries; §3.13(e) is what refers the module name space here.
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 3, "23.9"));
}

TEST(NameSpaceElaboration, RedeclarationOfVariableAsNetError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  reg v;\n"
      "  wire v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'v'", 3, "23.9"));
}

TEST(NameSpaceElaboration, RedeclarationOfNetAsVariableError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  wire w;\n"
      "  logic w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'w'", 3, "23.9"));
}

TEST(NameSpaceElaboration, TaskSameNameAsVariableError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic foo;\n"
             "  task foo; endtask\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'foo'", 3, "23.9"));
}

TEST(NameSpaceElaboration, NamedEventSameNameAsVariableError) {
  // §3.13(e): named events are unified with variables in the module name space,
  // so an event may not share a name with a variable in the same module.
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  event e;\n"
             "  logic e;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'e'", 3, "23.9"));
}

TEST(NameSpaceElaboration, TaskSameNameAsVariableInInterfaceError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("interface i;\n"
             "  logic foo;\n"
             "  task foo; endtask\n"
             "endinterface\n"
             "module m;\n"
             "  i inst();\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'foo'", 3, "23.9"));
}

TEST(NameSpaceElaboration, GateInstanceSameNameAsOutputNetError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  wire a, b;\n"
             "  wire g;\n"
             "  and g(g, a, b);\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "gate instance name 'g' conflicts with its output "
                            "net",
                            4, "23.9"));
}

TEST(NameSpaceElaboration, NamedBlockSameNameAsVariableError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic blk;\n"
             "  initial begin : blk\n"
             "    int y;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'blk'", 3, "23.9"));
}

TEST(NameSpaceElaboration, ModuleInstanceSameNameAsVariableError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module child; endmodule\n"
             "module top;\n"
             "  logic u;\n"
             "  child u();\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'u'", 4, "23.9"));
}

TEST(NameSpaceElaboration, BlockNameSpaceDuplicateDeclarationError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  for (genvar i = 0; i < 2; i = i + 1) begin : g\n"
             "    logic x;\n"
             "    wire x;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 4, "23.9"));
}

TEST(NameSpaceElaboration, DuplicateLocalInSameProceduralBlockError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    int x;\n"
             "    int x;\n"
             "  end\n"
             "endmodule\n",
             f));
  // A procedural block is checked by CheckOneBlockLocals in
  // src/elaborator/elaborator_scope_rules.cpp, which reports under §23.9; only
  // a subroutine body reports the same clash under §3.13.
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 4, "23.9"));
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
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  function int f();\n"
             "    int x;\n"
             "    int x;\n"
             "    return 0;\n"
             "  endfunction\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 4, "3.13"));
}

TEST(NameSpaceElaboration, TaskBodyDuplicateLocalError) {
  // §3.13(f): the task construct likewise introduces a block name space.
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  task t();\n"
             "    int y;\n"
             "    int y;\n"
             "  endtask\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'y'", 4, "3.13"));
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
