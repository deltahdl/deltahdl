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

}  // namespace
