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

}  // namespace
