#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(DpiExportedTaskElab, AnExportOfAnUndefinedTaskIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      export "DPI-C" task t;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 't', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            3, "35.7"));
}

TEST(DpiExportedTaskElab, AnExportOfAnotherModulesTaskIsError) {
  ElabFixture f;
  Elaborate(R"(
    module other;
      task t; endtask
    endmodule
    module m;
      export "DPI-C" task t;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 't', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            6, "35.7"));
}

TEST(DpiExportedTaskElab, APackageExportOfItsOwnTaskIsOk) {
  ElabFixture f;
  Elaborate(R"(
    package p;
      export "DPI-C" task t;
      task t; endtask
    endpackage
    module m;
      import p::*;
      initial t;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportedTaskElab, APackageExportOfATaskItDoesNotDefineIsError) {
  ElabFixture f;
  Elaborate(R"(
    package p;
      export "DPI-C" task t;
    endpackage
    module m;
      task t; endtask
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 't', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            3, "35.7"));
}

TEST(DpiExportedTaskElab, AnInterfaceExportOfItsOwnTaskIsOk) {
  ElabFixture f;
  Elaborate(R"(
    interface i;
      export "DPI-C" task t;
      task t; endtask
    endinterface
    module m;
      i u();
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportedTaskElab, AnInterfaceExportOfATaskItDoesNotDefineIsError) {
  ElabFixture f;
  Elaborate(R"(
    interface i;
      export "DPI-C" task t;
    endinterface
    module m;
      task t; endtask
      i u();
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 't', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            3, "35.7"));
}

TEST(DpiExportedTaskElab, AProgramExportOfItsOwnTaskIsOk) {
  ElabFixture f;
  Elaborate(R"(
    program p;
      export "DPI-C" task t;
      task t; endtask
    endprogram
    module m;
      p u();
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportedTaskElab, AProgramExportOfATaskItDoesNotDefineIsError) {
  ElabFixture f;
  Elaborate(R"(
    program p;
      export "DPI-C" task t;
    endprogram
    module m;
      task t; endtask
      p u();
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 't', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            3, "35.7"));
}

TEST(DpiExportedTaskElab, ACompilationUnitExportOfItsOwnTaskIsOk) {
  ElabFixture f;
  Elaborate(R"(
    export "DPI-C" task t;
    task t; endtask
    module m;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportedTaskElab, ACompilationUnitExportOfATaskItDoesNotDefineIsError) {
  ElabFixture f;
  Elaborate(R"(
    export "DPI-C" task t;
    module m;
      task t; endtask
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 't', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            2, "35.7"));
}

TEST(DpiExportedTaskElab, AGenerateBlockExportOfItsOwnTaskIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      if (1) begin : g
        export "DPI-C" task t;
        task t; endtask
      end
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(DpiExportedTaskElab, AGenerateBlockExportOfTheModulesTaskIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      task t; endtask
      if (1) begin : g
        export "DPI-C" task t;
      end
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "DPI export names 't', which is not a "
                            "SystemVerilog function or task defined in the "
                            "enclosing scope",
                            5, "35.7"));
}

}  // namespace
