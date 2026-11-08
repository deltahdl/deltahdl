#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(DpiImportedSubroutineUsage, FunctionCannotEnableAnImportedTask) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" task sv_wait(input int cycles);
      function void g();
        sv_wait(3);
      endfunction
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function cannot enable a task", 5, "13.4"));
}

TEST(DpiImportedSubroutineUsage, FunctionCanCallAnImportedFunction) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_get(input int a);
      function int g();
        return sv_get(3);
      endfunction
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiImportedSubroutineUsage, TaskCanEnableAnImportedTask) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" task sv_wait(input int cycles);
      task t();
        sv_wait(3);
      endtask
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiImportCallArgs, TooManyActualsToAnImportedFunctionIsReported) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int a);
      int r;
      initial r = sv_f(1, 2);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "too many arguments to 'sv_f': expected 1, got 2",
                            5, "13.5"));
}

TEST(DpiImportCallArgs, AnOmittedActualWithNoDefaultIsReported) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int a);
      int r;
      initial r = sv_f();
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "missing argument 'a' in call to 'sv_f'", 5,
                            "13.5.3"));
}

TEST(DpiImportCallArgs, AnUnknownNamedActualIsReported) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int a);
      int r;
      initial r = sv_f(.nosuch(1));
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "no parameter 'nosuch' in 'sv_f'", 5, "13.5.4"));
}

TEST(DpiImportCallArgs, AVoidImportedFunctionUsedAsAnOperandIsReported) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function void sv_v(input int a);
      int r;
      initial r = sv_v(1);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function 'sv_v' used as expression operand",
                            5, "13.4.1"));
}

TEST(DpiImportCallArgs, AWellFormedImportCallIsAccepted) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int a);
      int r;
      initial r = sv_f(1);
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiImportCallArgs, AnOmittedActualWithADefaultIsAccepted) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int a = 7);
      int r;
      initial r = sv_f();
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiImportClassification, AnImportedSubroutineIsNotALetDeclaration) {
  ElabFixture f;
  auto* design = Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int a);
    endmodule
  )",
                           f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  const RtlirModule* mod = design->top_modules[0];
  bool among_lets = false;
  for (const ModuleItem* item : mod->let_decls) {
    if (item->kind == ModuleItemKind::kDpiImport) among_lets = true;
  }
  EXPECT_FALSE(among_lets);
}

TEST(DpiImportClassification, AnImportedSubroutineIsCarriedOnItsOwnVector) {
  ElabFixture f;
  auto* design = Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int a);
    endmodule
  )",
                           f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  const RtlirModule* mod = design->top_modules[0];
  bool carries_import = false;
  for (const ModuleItem* item : mod->dpi_import_decls) {
    if (item->kind == ModuleItemKind::kDpiImport && item->name == "sv_f") {
      carries_import = true;
    }
  }
  EXPECT_TRUE(carries_import);
}

TEST(DpiImportClassification, ALetDeclarationStaysAmongTheLetDeclarations) {
  ElabFixture f;
  auto* design = Elaborate(R"(
    module m;
      let twice(x) = x + x;
    endmodule
  )",
                           f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  const RtlirModule* mod = design->top_modules[0];
  bool carries_let = false;
  for (const ModuleItem* item : mod->let_decls) {
    if (item->kind == ModuleItemKind::kLetDecl && item->name == "twice") {
      carries_let = true;
    }
  }
  EXPECT_TRUE(carries_let);
}

TEST(DpiImportCallArgs, ADiscardedImportedFunctionResultIsWarnedAbout) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int a);
      initial sv_f(1);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "return value of nonvoid function 'sv_f' is "
                              "discarded; cast to void to silence this warning",
                              4, "13.4.1"));
}

TEST(DpiImportCallArgs, ParenthesesCannotBeOmittedOnANonvoidImportedFunction) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int a);
      initial sv_f;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot omit parentheses in call to nonvoid function 'sv_f'", 4,
      "13.5.5"));
}

TEST(DpiImportCallArgs,
     ParenthesesCannotBeOmittedWhenAnImportedTaskNeedsAnArg) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" task sv_wait(input int cycles);
      initial sv_wait;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot omit parentheses in call to 'sv_wait': not "
                            "all formal arguments have defaults",
                            4, "13.5.5"));
}

TEST(DpiImportCallArgs, ParenthesesMayBeOmittedOnAnImportedTaskWithDefaults) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" task sv_wait(input int cycles = 1);
      initial sv_wait;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
