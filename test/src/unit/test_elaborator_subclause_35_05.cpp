#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §35.5: "The usage of imported functions is similar as for native
// SystemVerilog functions." An imported task is used where a native task is
// used, so §13.4's "a function shall not enable a task" reaches a call to one.
// §35.5.1.1's note is what makes the rule matter here rather than being a
// formality: an imported task can consume time, which is the whole reason a
// function may not enable one.
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
  // The report stands at the call statement, line 5 of the literal above,
  // whose first line is the newline that follows R"(.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function cannot enable a task", 5, "13.4"));
}

// §35.5 makes an imported subroutine's usage that of the native form it was
// declared as, and §35.5.4 declares a task and a function apart. So the rule
// above turns on the declaration's keyword: a function calling an imported
// function is calling a function, and nothing is reported.
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

// §35.5's usage rule reaches a task calling an imported task as well, where the
// native form is legal and so this is. It is asserted because a repair that
// rejected every call to an imported task would satisfy the first case here
// and leave an imported task uncallable.
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

// §35.5: "The usage of imported functions is similar as for native
// SystemVerilog functions." §13.5 counts a call's actuals against the formal
// list §35.5.4 gave the import, so passing more than the declaration has is
// reported for an imported subroutine exactly as for a native one.
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
  // The report stands at the call, line 5 of the literal above, whose first
  // line is the newline that follows R"(.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "too many arguments to 'sv_f': expected 1, got 2",
                            5, "13.5"));
}

// §13.5.3 requires every formal without a default to be given an actual, and
// §35.5 makes an imported subroutine's call obey it. This is asserted apart
// from the arity case because the two are separate checks, and a repair
// reaching one need not reach the other.
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

// §13.5.4 rejects a named actual naming no formal of the subroutine. §35.5.4
// gives an import a formal list with names, so this is the case saying the
// formals were read rather than merely counted.
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

// §35.5.5 permits `void` as an imported function's result, and §13.4.1 forbids
// using a void function as an operand. The rule reaches an import because
// §35.5 makes its usage that of a native function.
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

// A call matching the declaration is accepted, which is what stops a repair
// from satisfying the four cases above by rejecting every call to an import.
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

// §35.5.4 permits a default value on an imported subroutine's formal, and
// §13.5.3 asks for an actual only where there is none. So omitting the actual
// for a formal that has one is well-formed, and the missing-argument case above
// must not fire here.
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

// §35.5.4 declares an imported subroutine and §11.12 declares a let, and the
// two are called differently: a let substitutes the expression its declaration
// writes, and an import calls a foreign function. An import carried among the
// let declarations is registered as a let by RegisterModuleSubroutines in
// src/simulator/lowerer_register.cpp, and the call is then expanded as a let
// over an expression an import declaration never writes.
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

// The declaration is carried rather than dropped: whatever registers a run's
// imports has to find it. Asserted apart from the case above, which a repair
// deleting the declaration outright would also satisfy.
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

// §11.12's let is unaffected: a module declaring one still carries it where the
// lowerer registers lets. Without this, moving every kind out of let_decls
// would satisfy both cases above.
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

// §13.4.1 warns that a non-void function called as a statement discards its
// result, and §35.5 makes an imported function's usage that of a native one, so
// the warning covers a call to one.
TEST(DpiImportCallArgs, ADiscardedImportedFunctionResultIsWarnedAbout) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      import "DPI-C" function int sv_f(input int a);
      initial sv_f(1);
    endmodule
  )",
            f, "m");
  // The report stands at the call, line 4 of the literal above, whose first
  // line is the newline that follows R"(.
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "return value of nonvoid function 'sv_f' is "
                              "discarded; cast to void to silence this warning",
                              4, "13.4.1"));
}

// §13.5.5 permits the parentheses of a call to be omitted only for a task or a
// void function. §35.5.5 has an imported function state its result type, so a
// non-void one is decided by that type here as a native function is.
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

// §13.5.5's second condition: the parentheses may be omitted only where every
// formal has a default. An imported task passes the first condition by the
// keyword §35.5.4 declared it with and is decided by this one, which is why it
// is asserted apart from the case above.
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

// §13.5.5 is satisfied where the imported task's every formal has a default, so
// the omission stands. Without this a repair rejecting every paren-omitted call
// to an import would satisfy the two cases above.
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
