#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

bool RunAnnexDSource(SimFixture& f, const std::string& src) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return false;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return true;
}

std::string AsTask(const std::string& call) {
  return "module t;\n"
         "  initial " +
         call +
         ";\n"
         "endmodule\n";
}

std::string AsFunction(const std::string& call) {
  return "module t;\n"
         "  int v;\n"
         "  initial v = " +
         call +
         ";\n"
         "endmodule\n";
}

std::string NotAvailable(const std::string& name, const std::string& sub) {
  return name + " is the optional system task or system function " + sub +
         " describes, which Annex D.1 allows an implementation to be without; "
         "this implementation is one without it";
}

TEST(OptionalSystemTasksGeneral, AnUnavailableKeyTaskIsReportedUnderD1) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$key")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotAvailable("$key", "D.5"),
                            2, "D.1"));
}

TEST(OptionalSystemTasksGeneral, AnUnavailableInputTaskIsReportedUnderD1) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$input(\"cmds.txt\")")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotAvailable("$input", "D.4"),
                            2, "D.1"));
}

TEST(OptionalSystemTasksGeneral, AnUnavailableSaveTaskIsReportedUnderD1) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$save(\"state.dat\")")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotAvailable("$save", "D.9"),
                            2, "D.1"));
}

TEST(OptionalSystemTasksGeneral, AnUnavailableRestartTaskIsReportedUnderD1) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$restart(\"state.dat\")")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            NotAvailable("$restart", "D.9"), 2, "D.1"));
}

TEST(OptionalSystemTasksGeneral, AnUnavailableIncsaveTaskIsReportedUnderD1) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$incsave(\"inc1.dat\")")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            NotAvailable("$incsave", "D.9"), 2, "D.1"));
}

TEST(OptionalSystemTasksGeneral, AnUnavailableNokeyTaskIsReportedUnderD1) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$nokey")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotAvailable("$nokey", "D.5"),
                            2, "D.1"));
}

TEST(OptionalSystemTasksGeneral, AnUnavailableResetTaskIsReportedUnderD1) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$reset(1, 42)")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotAvailable("$reset", "D.8"),
                            2, "D.1"));
}

TEST(OptionalSystemTasksGeneral, AnUnavailableResetCountIsReportedUnderD1) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsFunction("$reset_count")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            NotAvailable("$reset_count", "D.8"), 3, "D.1"));
}

TEST(OptionalSystemTasksGeneral, AnUnavailableResetValueIsReportedUnderD1) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsFunction("$reset_value")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            NotAvailable("$reset_value", "D.8"), 3, "D.1"));
}

TEST(OptionalSystemTasksGeneral, AnAvailableOptionalTaskIsNotReported) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$list")));
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OptionalSystemTasksGeneral, ANameOutsideAnnexDKeepsTheCatalogueReport) {
  SimFixture f;
  ASSERT_TRUE(RunAnnexDSource(f, AsTask("$keyboard")));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$keyboard is not a system task or system "
                            "function this tool implements",
                            2, "20.1"));
}

struct UnavailableCall {
  const char* statement;
  const char* name;
  const char* subclause;
};

const UnavailableCall kUnavailableCalls[] = {
    {"$key", "$key", "D.5"},
    {"$nokey", "$nokey", "D.5"},
    {"$input(\"cmds.txt\")", "$input", "D.4"},
    {"$save(\"state.dat\")", "$save", "D.9"},
    {"$restart(\"state.dat\")", "$restart", "D.9"},
    {"$incsave(\"inc1.dat\")", "$incsave", "D.9"},
    {"$reset", "$reset", "D.8"},
    {"$reset(0)", "$reset", "D.8"},
    {"$reset(1, 42, 3)", "$reset", "D.8"},
    {"v = $reset_count", "$reset_count", "D.8"},
    {"v = $reset_value", "$reset_value", "D.8"},
};

TEST(OptionalSystemTasksGeneral, AnUnavailableCallIsReportedWhereverItRuns) {
  const char* const kPlaces[] = {
      "module t;\n  int v;\n  initial begin\n    %;\n  end\nendmodule\n",
      "module t;\n  int v;\n  task automatic tk;\n    %;\n  endtask\n"
      "  initial tk();\nendmodule\n",
      "module t;\n  int v;\n  function automatic void fn;\n    %;\n"
      "  endfunction\n  initial fn();\nendmodule\n",
      "program t;\n  int v;\n  initial begin\n    %;\n  end\nendprogram\n",
      "class c;\n  int v;\n  function void m();\n    %;\n  endfunction\n"
      "endclass\nmodule t;\n  initial begin\n    c o = new;\n    o.m();\n"
      "  end\nendmodule\n",
      "package pk;\n  int v;\n  function automatic void f();\n    %;\n"
      "  endfunction\nendpackage\nmodule t;\n  initial pk::f();\nendmodule\n",
  };
  for (const char* place : kPlaces) {
    for (const auto& call : kUnavailableCalls) {
      std::string src = place;
      src.replace(src.find('%'), 1, call.statement);
      SimFixture f;
      ASSERT_TRUE(RunAnnexDSource(f, src)) << src;
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                NotAvailable(call.name, call.subclause),
                                LineHolding(src, call.statement), "D.1"))
          << src;
    }
  }
}

}  // namespace
