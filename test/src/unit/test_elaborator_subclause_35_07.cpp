#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(DpiExportElab, OmittedCIdentifierDefaultsToFunctionIdentifier) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_func(); endfunction
      export "DPI-C" function sv_func;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportElab, ExplicitCIdentifierClashesWithImplicitInSameScopeIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void link();  endfunction
      function void other(); endfunction
      export "DPI-C" function link;
      export "DPI-C" link = function other;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export linkage name 'link' already declared "
                            "in this scope",
                            6, "35.4"));
}

TEST(DpiExportElab, DuplicateExplicitCIdentifierInSameScopeIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_a(); endfunction
      function void sv_b(); endfunction
      export "DPI-C" link = function sv_a;
      export "DPI-C" link = function sv_b;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export linkage name 'link' already declared "
                            "in this scope",
                            6, "35.4"));
}

TEST(DpiExportElab, ExportBeforeFunctionDefinitionInSameScopeIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      export "DPI-C" function sv_func;
      function void sv_func(); endfunction
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportElab, TwoExportsOfSameSvFunctionWithDifferentCIdsIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_func(); endfunction
      export "DPI-C" first = function sv_func;
      export "DPI-C" second = function sv_func;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'sv_func' is already "
                            "exported in this scope",
                            5, "35.7"));
}

TEST(DpiExportElab, ExportedFunctionWithRefArgumentIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_func(ref int x); endfunction
      export "DPI-C" function sv_func;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'sv_func' has a ref "
                            "argument and therefore cannot be exported",
                            4, "35.7"));
}

TEST(DpiExportElab, ExportedTaskWithRefArgumentSaysTask) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      task sv_task(ref int x); endtask
      export "DPI-C" task sv_task;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog task 'sv_task' has a ref "
                            "argument and therefore cannot be exported",
                            4, "35.7"));
}

TEST(DpiExportElab, ExportOfUndefinedFunctionInScopeIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      export "DPI-C" function not_defined_here;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 'not_defined_here', which is not "
                            "a SystemVerilog function or task defined in the "
                            "enclosing scope",
                            3, "35.7"));
}

TEST(DpiExportElab, ExportOfFunctionDefinedInDifferentModuleIsError) {
  ElabFixture f;
  Elaborate(R"(
    module other;
      function void sv_func(); endfunction
    endmodule

    module m;
      export "DPI-C" function sv_func;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 'sv_func', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            7, "35.7"));
}

TEST(DpiExportElab, ExportInAPackageOfAFunctionThePackageDoesNotDefineIsError) {
  ElabFixture f;
  Elaborate(R"(
    package p;
      export "DPI-C" function sv_f;
    endpackage
    module m;
      function int sv_f(input int x);
      endfunction
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 'sv_f', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            3, "35.7"));
}

TEST(DpiExportElab, AnExportDeclarationIsNotAmongTheLetDeclarations) {
  ElabFixture f;
  auto* design = Elaborate(R"(
    module m;
      function int sv_func();
      endfunction
      export "DPI-C" function sv_func;
    endmodule
  )",
                           f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  for (const ModuleItem* item : design->top_modules[0]->let_decls) {
    EXPECT_NE(item->kind, ModuleItemKind::kDpiExport);
  }
}

TEST(DpiExportElab, AnExportDeclarationIsAmongTheExportDeclarations) {
  ElabFixture f;
  auto* design = Elaborate(R"(
    module m;
      function int sv_func();
      endfunction
      export "DPI-C" function sv_func;
    endmodule
  )",
                           f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  bool carries_export = false;
  for (const ModuleItem* item : design->top_modules[0]->dpi_export_decls) {
    if (item->kind == ModuleItemKind::kDpiExport && item->name == "sv_func") {
      carries_export = true;
    }
  }
  EXPECT_TRUE(carries_export);
}

TEST(DpiExportElab, ExportOfAnOutOfBlockClassMethodIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      class C;
        extern function int foo();
      endclass
      function int C::foo();
        return 42;
      endfunction
      export "DPI-C" function foo;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'foo' is a member of class "
                            "'C' and class member functions cannot be exported",
                            9, "35.7"));
}

TEST(DpiExportElab, ExportInAnInterfaceOfAFunctionItDoesNotDefineIsError) {
  ElabFixture f;
  Elaborate(R"(
    interface i;
      export "DPI-C" function sv_func;
    endinterface
    module m;
      function int sv_func();
      endfunction
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 'sv_func', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            3, "35.7"));
}

TEST(DpiExportElab, APackageExportWrittenBeforeItsFunctionIsOk) {
  ElabFixture f;
  Elaborate(R"(
    package p;
      export "DPI-C" function f;
      function int f(); return 1; endfunction
    endpackage
    module m;
      import p::*;
      int x = f();
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportElab, AnInterfaceExportWrittenBeforeItsFunctionIsOk) {
  ElabFixture f;
  Elaborate(R"(
    interface i;
      export "DPI-C" function f;
      function int f(); return 1; endfunction
    endinterface
    module m;
      i u();
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportElab, AProgramExportWrittenBeforeItsFunctionIsOk) {
  ElabFixture f;
  Elaborate(R"(
    program p;
      export "DPI-C" function f;
      function int f(); return 1; endfunction
    endprogram
    module m;
      p u();
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportElab, AGenerateBlockExportWrittenBeforeItsFunctionIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      if (1) begin : g
        export "DPI-C" function f;
        function int f(); return 1; endfunction
      end
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportElab, ACompilationUnitExportWrittenBeforeItsFunctionIsOk) {
  ElabFixture f;
  Elaborate(R"(
    export "DPI-C" function f;
    function int f(); return 1; endfunction
    module m;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportElab, AProgramExportOfAModulesFunctionIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function int f(); return 1; endfunction
      p u();
    endmodule
    program p;
      export "DPI-C" function f;
    endprogram
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 'f', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            7, "35.7"));
}

TEST(DpiExportElab, ACompilationUnitExportOfAModulesFunctionIsError) {
  ElabFixture f;
  Elaborate(R"(
    export "DPI-C" function f;
    module m;
      function int f(); return 1; endfunction
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 'f', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            2, "35.7"));
}

TEST(DpiExportElab, AGenerateBlockExportOfTheEnclosingModulesFunctionIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function int f(); return 1; endfunction
      if (1) begin : g
        export "DPI-C" function f;
      end
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 'f', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            5, "35.7"));
}

TEST(DpiExportElab, AModuleExportOfItsGenerateBlocksFunctionIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      if (1) begin : g
        function int f(); return 1; endfunction
      end
      export "DPI-C" function f;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 'f', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            6, "35.7"));
}

TEST(DpiExportElab, AnExportOfAWildcardImportedFunctionIsError) {
  ElabFixture f;
  Elaborate(R"(
    package p;
      function int f(); return 1; endfunction
    endpackage
    module m;
      import p::*;
      export "DPI-C" function f;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 'f', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            7, "35.7"));
}

TEST(DpiExportElab, AnExportOfAnExplicitlyImportedFunctionIsError) {
  ElabFixture f;
  Elaborate(R"(
    package p;
      function int f(); return 1; endfunction
    endpackage
    module m;
      import p::f;
      export "DPI-C" function f;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 'f', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            7, "35.7"));
}

TEST(DpiExportElab, AnExportOfAnAutomaticFunctionIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function automatic int f(); return 1; endfunction
      export "DPI-C" function f;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportElab, AnExportOfAFunctionInAnAutomaticModuleIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module automatic m;
      function int f(); return 1; endfunction
      export "DPI-C" function f;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportElab, TwoDefaultedExportsOfOneFunctionAreAnError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function int f(); return 1; endfunction
      export "DPI-C" function f;
      export "DPI-C" function f;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'f' is already exported "
                            "in this scope; only one export declaration per "
                            "function is permitted",
                            5, "35.7"));
}

TEST(DpiExportElab, TwoExportsOfOneFunctionInAPackageAreAnError) {
  ElabFixture f;
  Elaborate(R"(
    package p;
      function int f(); return 1; endfunction
      export "DPI-C" a = function f;
      export "DPI-C" b = function f;
    endpackage
    module m;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'f' is already exported "
                            "in this scope; only one export declaration per "
                            "function is permitted",
                            5, "35.7"));
}

TEST(DpiExportElab, TwoExportsOfOneFunctionInAnInterfaceAreAnError) {
  ElabFixture f;
  Elaborate(R"(
    interface i;
      function int f(); return 1; endfunction
      export "DPI-C" a = function f;
      export "DPI-C" b = function f;
    endinterface
    module m;
      i u();
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'f' is already exported "
                            "in this scope; only one export declaration per "
                            "function is permitted",
                            5, "35.7"));
}

TEST(DpiExportElab, TwoExportsOfOneFunctionInAProgramAreAnError) {
  ElabFixture f;
  Elaborate(R"(
    program p;
      function int f(); return 1; endfunction
      export "DPI-C" a = function f;
      export "DPI-C" b = function f;
    endprogram
    module m;
      p u();
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'f' is already exported "
                            "in this scope; only one export declaration per "
                            "function is permitted",
                            5, "35.7"));
}

TEST(DpiExportElab, TwoExportsOfOneFunctionInAGenerateBlockAreAnError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      if (1) begin : g
        function int f(); return 1; endfunction
        export "DPI-C" a = function f;
        export "DPI-C" b = function f;
      end
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'f' is already exported "
                            "in this scope; only one export declaration per "
                            "function is permitted",
                            6, "35.7"));
}

TEST(DpiExportElab, TwoExportsOfOneFunctionInTheCompilationUnitAreAnError) {
  ElabFixture f;
  Elaborate(R"(
    function int f(); return 1; endfunction
    export "DPI-C" a = function f;
    export "DPI-C" b = function f;
    module m;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'f' is already exported "
                            "in this scope; only one export declaration per "
                            "function is permitted",
                            4, "35.7"));
}

TEST(DpiExportElab, DISABLED_TheCIdentifierOfAnExportIsNoSystemVerilogName) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      int r;
      function int f(input int x); return x; endfunction
      export "DPI-C" c_f = function f;
      initial r = c_f(4);
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'c_f'",
                            6, "23.9"));
}

}  // namespace
