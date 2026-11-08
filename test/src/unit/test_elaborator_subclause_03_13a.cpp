#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

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
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag,
              TextOrigin::kPreprocessorOutput);
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
  EXPECT_TRUE(
      ElabOk("package p1; endpackage\n"
             "package p2; endpackage\n"
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

TEST(NameSpaceElaboration, OutOfBlockBodiesOfTwoClassesShareANameUnreported) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  extern virtual function int compute();\n"
             "endclass\n"
             "function int Base::compute(); return 12; endfunction\n"
             "class Derived extends Base;\n"
             "  extern virtual function int compute();\n"
             "endclass\n"
             "function int Derived::compute(); return 21; endfunction\n"
             "module m; endmodule\n",
             f));
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "redeclaration of 'compute' in compilation-unit scope", 8, "3.13"));
}

TEST(NameSpaceElaboration, FreeFunctionBesideAnOutOfBlockBodyStillChecked) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  extern function int compute();\n"
             "endclass\n"
             "function int Base::compute(); return 12; endfunction\n"
             "function int compute(); return 1; endfunction\n"
             "function int compute(); return 2; endfunction\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "redeclaration of 'compute' in compilation-unit scope", 6, "3.13"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 'foo' in compilation-unit scope",
                            1, "3.13"));
}

TEST(NameSpaceElaboration, DuplicateCuScopeTask) {
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 3, "6.5"));
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
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'v'", 3, "6.5"));
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
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'w'", 3, "6.5"));
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
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  event e;\n"
             "  logic e;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'e'", 3, "6.5"));
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
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 4, "6.5"));
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

TEST(NameSpaceElaboration, SameLocalNameInFunctionNestedBlockOk) {
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
  EXPECT_TRUE(
      ElabOk("module m(data);\n"
             "  input data;\n"
             "  wire data;\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, AttributeNameCoincidesWithVariableElaboratesOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  (* keep *) logic keep;\n"
             "endmodule\n"));
}

}  // namespace
