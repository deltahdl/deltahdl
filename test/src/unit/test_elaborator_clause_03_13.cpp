#include "fixture_elaborator.h"

namespace {

TEST(ElabClause03, Cl3_13_DistinctNamesInModuleScope) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a;\n"
             "  logic b;\n"
             "  wire c;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_13_SameNameDifferentModulesElab) {
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

TEST(ElabClause03, Cl3_13_RedeclVarInModuleScope) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic x;\n"
             "  logic x;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_13_RedeclNetInModuleScope) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  wire w;\n"
             "  wire w;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_13_DuplicateModuleDefinition) {
  EXPECT_FALSE(
      ElabOk("module m; endmodule\n"
             "module m; endmodule\n"));
}

TEST(ElabClause03, Cl3_13_ModuleAndInterfaceSameName) {
  ElabFixture f;
  ElaborateSrc(
      "module foo; endmodule\n"
      "interface foo; endinterface\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ElabClause03, Cl3_13_ModuleAndProgramSameName) {
  ElabFixture f;
  ElaborateSrc(
      "module bar; endmodule\n"
      "program bar; endprogram\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ElabClause03, Cl3_13_DuplicatePackageDefinition) {
  EXPECT_FALSE(
      ElabOk("package p; endpackage\n"
             "package p; endpackage\n"
             "module m; endmodule\n"));
}

TEST(ElabClause03, Cl3_13_DistinctDefinitionNamesOk) {
  EXPECT_TRUE(
      ElabOk("module m; endmodule\n"
             "interface ifc; endinterface\n"
             "program p; endprogram\n"));
}

TEST(ElabClause03, Cl3_13_ModuleNameSpaceCoexist) {
  EXPECT_TRUE(
      ElabOk("module sub; endmodule\n"
             "module m;\n"
             "  parameter P = 1;\n"
             "  logic data;\n"
             "  wire net;\n"
             "  sub u0();\n"
             "endmodule\n"));
}

}  // namespace
