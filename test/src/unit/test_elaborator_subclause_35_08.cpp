#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §35.8: a foreign language may call SystemVerilog tasks as it calls functions,
// and such tasks are what the clause calls exported tasks. A.2.6 writes the
// exported-task form with the `task` keyword and its own task_identifier, so an
// export declaration's keyword says which kind of subroutine it names, and the
// cases below hold a declaration to that.

TEST(DpiExportedTaskElab, ExportOfATaskWrittenWithTheTaskKeywordIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      task sv_task;
      endtask
      export "DPI-C" task sv_task;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportedTaskElab, ExportOfAFunctionWrittenWithTheTaskKeywordIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function int sv_func();
      endfunction
      export "DPI-C" task sv_func;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "DPI export declares 'sv_func' with the 'task' "
                    "keyword, but 'sv_func' is a SystemVerilog function",
                    5, "35.8"));
}

TEST(DpiExportedTaskElab, ExportOfATaskWrittenWithTheFunctionKeywordIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      task sv_task;
      endtask
      export "DPI-C" function sv_task;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export declares 'sv_task' with the 'function' "
                            "keyword, but 'sv_task' is a SystemVerilog task",
                            5, "35.8"));
}

// §35.8: everything §35.7 says of exported functions holds for exported tasks
// too. §35.7 permits only one export declaration per subroutine in a scope, and
// the report a user who wrote `task` reads says task, so that it does not send
// them looking for a function they never declared.
TEST(DpiExportedTaskElab, TwoExportsOfOneTaskSayTask) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      task sv_task;
      endtask
      export "DPI-C" a = task sv_task;
      export "DPI-C" b = task sv_task;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog task 'sv_task' is already exported "
                            "in this scope; only one export declaration per "
                            "task is permitted",
                            6, "35.7"));
}

// §35.8 carries §35.7's prohibition on exporting a class member function to
// exported tasks, and the report names the kind the declaration reached.
TEST(DpiExportedTaskElab, ExportOfAnOutOfBlockClassMethodTaskSaysTask) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      class C;
        extern task run();
      endclass
      task C::run();
      endtask
      export "DPI-C" task run;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog task 'run' is a member of class 'C' "
                            "and class member functions cannot be exported",
                            8, "35.7"));
}

}  // namespace
