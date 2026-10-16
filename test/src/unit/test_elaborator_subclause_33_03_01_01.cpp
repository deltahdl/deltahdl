// Tests for IEEE 1800-2023 §33.3.1.1 (printed page 937) at the elaborator: of
// several cells of one name mapped into one library, the one encountered last
// is the one written there, and several modules of one name mapped into one
// library in a single invocation draw a warning. §33.3.1 compiles a file that
// no library claims into work, so two definitions of one name in one run share
// a library with or without a library map, and this clause, written for that
// case, governs it ahead of §3.13(a)'s general rule.

#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// The library holds the last m, so that is the m top.u binds.
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

// The earlier m is no longer in the library, so it roots no second top.
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

// The warning is for modules; two interfaces of one name are written over one
// another without it.
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

// A module and an interface of one name are two cells of one name in one
// library: the interface, encountered last, is what the library holds, and
// with only one of the two a module, nothing warns.
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

// The module encountered after a program of its name replaces the program, so
// the module is what roots the design.
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

}  // namespace
