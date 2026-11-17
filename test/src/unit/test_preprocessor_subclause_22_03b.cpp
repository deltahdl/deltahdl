#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"
#include "helpers_include_test_dir.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

class ResetallPlacement : public ::testing::Test {
 protected:
  void Run(const std::string& src) {
    auto fid = f_.mgr.AddFile("<test>", src);
    pp_.Preprocess(fid);
  }

  bool ReportedAt(int line) const {
    return ReportedError(f_.diag.Diagnostics(),
                         "`resetall illegal inside a design element", line,
                         "22.3");
  }

  bool Accepted() const { return !f_.diag.HasErrors(); }

  PreprocFixture f_;
  Preprocessor pp_{f_.mgr, f_.diag, {}};
};

TEST_F(ResetallPlacement, InsideAMacromoduleNestedInAModule) {
  Run("module outer;\nmacromodule inner;\n`resetall\nendmodule\nendmodule\n");
  EXPECT_TRUE(ReportedAt(3));
}

TEST_F(ResetallPlacement, InsideAProgramNestedInAModule) {
  Run("module outer;\nprogram p;\n`resetall\nendprogram\nendmodule\n");
  EXPECT_TRUE(ReportedAt(3));
}

TEST_F(ResetallPlacement, InsideAnInterfaceNestedInAModule) {
  Run("module outer;\ninterface i;\n`resetall\nendinterface\nendmodule\n");
  EXPECT_TRUE(ReportedAt(3));
}

TEST_F(ResetallPlacement, InsideACheckerNestedInAModule) {
  Run("module outer;\nchecker c;\n`resetall\nendchecker\nendmodule\n");
  EXPECT_TRUE(ReportedAt(3));
}

TEST_F(ResetallPlacement, InsideAnInterfaceNestedInAnInterface) {
  Run("interface outer;\ninterface inner;\n`resetall\nendinterface\n"
      "endinterface\n");
  EXPECT_TRUE(ReportedAt(3));
}

TEST_F(ResetallPlacement, InsideAProgramNestedInAnInterface) {
  Run("interface outer;\nprogram p;\n`resetall\nendprogram\nendinterface\n");
  EXPECT_TRUE(ReportedAt(3));
}

TEST_F(ResetallPlacement, InsideACheckerNestedInAnInterface) {
  Run("interface outer;\nchecker c;\n`resetall\nendchecker\nendinterface\n");
  EXPECT_TRUE(ReportedAt(3));
}

TEST_F(ResetallPlacement, InsideACheckerNestedInAProgram) {
  Run("program outer;\nchecker c;\n`resetall\nendchecker\nendprogram\n");
  EXPECT_TRUE(ReportedAt(3));
}

TEST_F(ResetallPlacement, InsideACheckerNestedInAPackage) {
  Run("package p;\nchecker c;\n`resetall\nendchecker\nendpackage\n");
  EXPECT_TRUE(ReportedAt(3));
}

TEST_F(ResetallPlacement, DISABLED_InAPackageAfterAnAnonymousProgram) {
  Run("package p;\nprogram;\nendprogram\n`resetall\nendpackage\n");
  EXPECT_TRUE(ReportedAt(4));
}

TEST_F(ResetallPlacement, InAPackageAfterASpacedAnonymousProgram) {
  Run("package p;\nprogram ;\nendprogram\n`resetall\nendpackage\n");
  EXPECT_TRUE(ReportedAt(4));
}

TEST_F(ResetallPlacement, FromAFileIncludedInsideAModule) {
  IncludeTestDir tmp;
  tmp.WriteFile("reset.svh", "`resetall\n");
  auto fid = f_.mgr.AddFile((tmp.dir / "top.sv").string(),
                            "module m;\n`include \"reset.svh\"\nendmodule\n");
  pp_.Preprocess(fid);
  EXPECT_TRUE(ReportedAt(1));
}

TEST_F(ResetallPlacement, FromAMacroExpandedInsideAModule) {
  Run("`define R `resetall\nmodule m;\n`R\nendmodule\n");
  EXPECT_TRUE(ReportedAt(3));
}

TEST_F(ResetallPlacement, InsideAnInitialBlock) {
  Run("module m;\ninitial begin\n`resetall\nend\nendmodule\n");
  EXPECT_TRUE(ReportedAt(3));
}

TEST_F(ResetallPlacement, InsideAClassAtCompilationUnitScope) {
  Run("class c;\n`resetall\nendclass\n");
  EXPECT_TRUE(Accepted());
}

TEST_F(ResetallPlacement, InsideAFunctionAtCompilationUnitScope) {
  Run("function void f();\n`resetall\nendfunction\n");
  EXPECT_TRUE(Accepted());
}

TEST_F(ResetallPlacement, InAFileThatOpensBeforeAnEarlierFileClosesAModule) {
  auto first = f_.mgr.AddFile("a.sv", "module m;\n");
  auto second = f_.mgr.AddFile("b.sv", "`resetall\nendmodule\n");
  pp_.Preprocess(first);
  pp_.Preprocess(second);
  EXPECT_TRUE(ReportedAt(1));
}

TEST_F(ResetallPlacement, AtTheHeadOfAFileAfterAnEarlierFileClosedItsModule) {
  auto first = f_.mgr.AddFile("a.sv", "module m;\nendmodule\n");
  auto second = f_.mgr.AddFile("b.sv", "`resetall\nmodule n;\nendmodule\n");
  pp_.Preprocess(first);
  pp_.Preprocess(second);
  EXPECT_TRUE(Accepted());
}

TEST_F(ResetallPlacement, AfterAnExternModule) {
  Run("extern module e(input a);\n`resetall\nmodule m;\nendmodule\n");
  EXPECT_TRUE(Accepted());
}

TEST_F(ResetallPlacement, AfterALabelledEndmodule) {
  Run("module m;\nendmodule : m\n`resetall\n");
  EXPECT_TRUE(Accepted());
}

TEST_F(ResetallPlacement, InAnExcludedBranchInsideAModule) {
  Run("module m;\n`ifdef NO\n`resetall\n`endif\nendmodule\n");
  EXPECT_TRUE(Accepted());
}

TEST_F(ResetallPlacement, InACommentInsideAModule) {
  Run("module m;\n// `resetall\n/* `resetall */\nendmodule\n");
  EXPECT_TRUE(Accepted());
}

TEST_F(ResetallPlacement, InAStringInsideAModule) {
  Run("module m;\nstring s = \"`resetall\";\nendmodule\n");
  EXPECT_TRUE(Accepted());
}

TEST_F(ResetallPlacement, DISABLED_AfterAStringSpellingEndmodule) {
  Run("module m;\nstring s = \"endmodule\";\n`resetall\nendmodule\n");
  EXPECT_TRUE(ReportedAt(3));
}

TEST_F(ResetallPlacement, AfterTheEndmoduleFollowingAStringSpellingIt) {
  Run("module m;\nstring s = \"endmodule\";\nendmodule\n`resetall\n");
  EXPECT_TRUE(Accepted());
}

TEST_F(ResetallPlacement, DISABLED_AfterAModuleHeaderFromAMacro) {
  Run("`define B module q;\n`B\n`resetall\nendmodule\n");
  EXPECT_TRUE(ReportedAt(3));
}

TEST_F(ResetallPlacement, DISABLED_AfterAnEndmoduleFromAMacro) {
  Run("`define E endmodule\nmodule m;\n`E\n`resetall\n");
  EXPECT_TRUE(Accepted());
}

}  // namespace
