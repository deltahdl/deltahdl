#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §35.7: an export declaration's c_identifier is optional; when omitted it
// defaults to the SystemVerilog function_identifier. The elaborator therefore
// accepts an export declaration with no explicit c_identifier.
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

// §35.7: an export declaration whose explicit c_identifier matches the
// implicit (function-name) c_identifier of another export in the same scope
// collides. The rule covers explicit and implicit forms uniformly, so the
// elaborator rejects this mixed-form clash just like the two-explicit case.
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
  // The explicit/implicit c_identifier clash is reported under §35.4, whose
  // per-scope linkage-name rule the elaborator enforces for both forms.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export linkage name 'link' already declared "
                            "in this scope",
                            6, "35.4"));
}

// §35.7: "No two functions in the same SystemVerilog scope can be exported
// with the same explicit or implicit c_identifier." Two export declarations
// in one module that share an explicit c_identifier collide.
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
  // A repeated c_identifier is reported under §35.4, which states the
  // per-scope linkage-name rule §35.7 relies on.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export linkage name 'link' already declared "
                            "in this scope",
                            6, "35.4"));
}

// §35.7: "The export declaration and the definition of the corresponding
// SystemVerilog function can occur in any order." Placing the export
// declaration before the function definition is well-formed.
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

// §35.7: "Only one export declaration is permitted per SystemVerilog
// function." Two exports of the same SV function with distinct c_identifiers
// would slip through a c_identifier-only collision check, so the elaborator
// also dedupes on the underlying SystemVerilog routine.
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

// §35.7: an exported SystemVerilog function must obey the same restrictions
// on argument types as an imported function. The §35.5.4 prohibition on the
// ref qualifier in DPI declarations carries through, so a function with a
// ref argument cannot be exported.
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

// §35.8: "All aspects of exported functions described above in 35.7 apply to
// exported tasks", so the ref-argument prohibition of §35.7 refuses an exported
// task with a ref formal exactly as it refuses a function. §35.8 terms such a
// subroutine an exported task, so the report names the word the declaration
// used rather than calling it a function.
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

// §35.7: "Export declarations are allowed to occur only in the scope in which
// the function being exported is defined." An export that names an identifier
// with no matching SystemVerilog function in the enclosing module is rejected.
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

// §35.7: the function being exported must be defined in the same scope as
// the export declaration. Defining the function in a different module does
// not satisfy the scope requirement for an export sitting in another module.
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

// §35.7: "an export declaration is allowed only in the scope where the function
// being exported is defined." A package body is a scope of its own, so an
// export written there names a function that package must define, and a
// function of that name defined in a module does not answer for it.
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

// §35.7: "Declaring a SystemVerilog function to be exported does not change its
// semantics or behavior from the SystemVerilog perspective." The elaborator
// keeps the export declaration out of the module's let declarations, whose
// entries a run resolves a call to before it reaches a function, so the
// exported function stays the thing its own name calls.
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

// The other half of that rule: the export declaration is still elaborated, and
// is reachable where §35.7's exports are held. Without this the case above
// would hold of an elaborator that dropped the declaration entirely.
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

// §35.7: "Class member functions cannot be exported, but all other
// SystemVerilog functions can be exported." §8.24 writes an out-of-block method
// body in the scope its class is declared in, under the bare method name, so
// such a definition sits among the scope's callables and an export naming it
// reaches a class member function.
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

// §35.7: "Export declarations are allowed to occur only in the scope in which
// the function being exported is defined." An interface is such a scope —
// A.1.4's module_common_item carries dpi_import_export into an interface body —
// so an export written in one names a function that interface must define.
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

}  // namespace
