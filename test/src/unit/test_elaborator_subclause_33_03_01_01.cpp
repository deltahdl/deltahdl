#include <gtest/gtest.h>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_separate_units.h"

using namespace delta;

namespace {

TEST(LibraryCellRewrite, TwoModulesOfOneNameInOneLibraryWarn) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("module m; endmodule\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "module 'm' is written to library 'work' more "
                              "than once in this invocation",
                              2, "33.3.1.1"));
}

TEST(LibraryCellRewrite, AThirdModuleOfTheNameWarnsAgain) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("module m; endmodule\n"
             "module m; endmodule\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "module 'm' is written to library 'work' more "
                              "than once in this invocation",
                              3, "33.3.1.1"));
}

TEST(LibraryCellRewrite, TheModuleEncounteredLastIsTheOneBound) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic a; endmodule\n"
      "module m; logic b; endmodule\n"
      "module top; m u(); endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  const RtlirModule* bound = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->loc.line, 2u);
}

TEST(LibraryCellRewrite, AnOverwrittenModuleIsNoTop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic a; endmodule\n"
      "module m; logic b; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->loc.line, 2u);
}

TEST(LibraryCellRewrite, TwoInterfacesOfOneNameNeitherErrNorWarn) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("interface ifc; endinterface\n"
             "interface ifc; endinterface\n"
             "module m; endmodule\n",
             f));
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(LibraryCellRewrite, TwoProgramsOfOneNameNeitherErrNorWarn) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("program pr; endprogram\n"
             "program pr; endprogram\n"
             "module m; endmodule\n",
             f));
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(LibraryCellRewrite, TwoPrimitivesOfOneNameNeitherErrNorWarn) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("primitive p(output y, input a);\n"
             "  table 0 : 1 ; 1 : 0 ; endtable\n"
             "endprimitive\n"
             "primitive p(output y, input a);\n"
             "  table 0 : 1 ; 1 : 0 ; endtable\n"
             "endprimitive\n"
             "module m; endmodule\n",
             f));
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(LibraryCellRewrite, AnInterfaceAfterAModuleOfItsNameReplacesIt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module foo; endmodule\n"
      "interface foo; endinterface\n"
      "module top; foo u(); endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(LibraryCellRewrite, AModuleAfterAProgramOfItsNameReplacesIt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program bar; endprogram\n"
      "module bar; endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->loc.line, 2u);
}

TEST(LibraryCellRewrite, APrimitiveAfterAModuleOfItsNameNeitherErrsNorWarns) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("module foo; endmodule\n"
             "primitive foo(output y, input a);\n"
             "  table 0 : 1 ; 1 : 0 ; endtable\n"
             "endprimitive\n"
             "module m; endmodule\n",
             f));
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(LibraryCellRewrite, TheCheckerEncounteredLastAcrossUnitsIsBound) {
  ElabFixture f;
  Elaborator elab(f.arena, f.diag,
                  ParseUnitsApart({"checker chk(input logic x);\n"
                                   "endchecker\n",
                                   "\n"
                                   "checker chk(input logic x);\n"
                                   "endchecker\n"
                                   "module top;\n"
                                   "  logic v;\n"
                                   "  chk c(v);\n"
                                   "endmodule\n"},
                                  f.mgr, f.arena, f.diag));
  auto* design = elab.Elaborate("top");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  const RtlirModule* bound = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(bound, nullptr);
  EXPECT_TRUE(bound->is_checker);
  EXPECT_EQ(bound->loc.line, 2u);
}

}  // namespace
