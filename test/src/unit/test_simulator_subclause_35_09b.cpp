#include <dlfcn.h>
#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

using ExportedTaskNoArgs = int (*)();
using ExportedVoidFunction = void (*)();

int g_return = -1;
int g_state = -1;
int g_second = -1;
int g_gives = 1;
bool g_ack = false;

void ResetC(int gives, bool ack) {
  g_return = -1;
  g_state = -1;
  g_second = -1;
  g_gives = gives;
  g_ack = ack;
  DpiSetCurrentDisabledState(false);
}

ExportedTaskNoArgs TaskWithNoArgsNamed(const char* name) {
  return reinterpret_cast<ExportedTaskNoArgs>(dlsym(RTLD_DEFAULT, name));
}

int CallTheLongExport() {
  ExportedTaskNoArgs sv_long = TaskWithNoArgsNamed("sv_long");
  if (sv_long == nullptr) return 0;
  g_return = sv_long();
  g_state = svIsDisabledState();
  return g_gives;
}

int ReadTheStateOnly() {
  g_state = svIsDisabledState();
  return 0;
}

int CallASecondExportAfterTheDisable() {
  CallTheLongExport();
  ExportedTaskNoArgs sv_second = TaskWithNoArgsNamed("sv_second");
  if (sv_second == nullptr) return 0;
  g_second = sv_second();
  return 1;
}

int KillThroughAnExportedFunction() {
  auto sv_kill =
      reinterpret_cast<ExportedVoidFunction>(dlsym(RTLD_DEFAULT, "sv_kill"));
  if (sv_kill == nullptr) return -1;
  sv_kill();
  g_state = svIsDisabledState();
  if (g_ack) svAckDisabledState();
  return 3;
}

int WriteThenWaitInTheExport(int* out) {
  *out = 77;
  return CallTheLongExport();
}

int WriteNine(int* out) {
  *out = 9;
  return 0;
}

uint64_t ValueOf(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

std::string FatalOf(SimFixture& f) {
  DpiRuntime* rt = f.ctx.GetDpiRuntime();
  if (rt == nullptr || !rt->DisableProtocolFatalErrorIssued()) return "";
  return rt->DisableProtocolFatalError();
}

void RunLong(const std::string& src, SimFixture& f, const char* dir) {
  RunWithImportsBound(
      src, f, {{"c_disabled", reinterpret_cast<void*>(&CallTheLongExport)}},
      dir);
}

constexpr const char* kLongExport =
    "  export \"DPI-C\" task sv_long;\n"
    "  import \"DPI-C\" context task c_disabled();\n"
    "  task sv_long(); #100; endtask\n";

TEST(DpiDisableFromADesign, DISABLED_ADisableNamingTheImportedTaskDisablesIt) {
  ResetC(1, false);
  SimFixture f;
  RunLong(std::string("module top;\n") + kLongExport +
              "  int t;\n"
              "  initial begin\n"
              "    fork c_disabled(); join_none\n"
              "    #5 disable c_disabled;\n"
              "    t = $time;\n"
              "  end\n"
              "endmodule\n",
          f, "subclause_35_09_disable_the_import");
  EXPECT_EQ(g_return, 1);
  EXPECT_EQ(g_state, 1);
  EXPECT_EQ(ValueOf(f, "t"), 5U);
  EXPECT_EQ(FatalOf(f), "");
}

TEST(DpiDisableFromADesign, ADisableNamingATaskThatCallsTheImportDisablesIt) {
  ResetC(1, false);
  SimFixture f;
  RunLong(std::string("module top;\n") + kLongExport +
              "  task outer(); c_disabled(); endtask\n"
              "  int t;\n"
              "  initial begin\n"
              "    fork outer(); join_none\n"
              "    #5 disable outer;\n"
              "    t = $time;\n"
              "  end\n"
              "endmodule\n",
          f, "subclause_35_09_disable_a_caller_task");
  EXPECT_EQ(g_return, 1);
  EXPECT_EQ(g_state, 1);
  EXPECT_EQ(ValueOf(f, "t"), 5U);
  EXPECT_EQ(FatalOf(f), "");
}

TEST(DpiDisableFromADesign, ADisableOutsideTheCallChainLeavesTheImportAlone) {
  ResetC(0, false);
  SimFixture f;
  RunLong(std::string("module top;\n") + kLongExport +
              "  int t;\n"
              "  initial begin\n"
              "    fork\n"
              "      begin : blk c_disabled(); t = $time; end\n"
              "      begin : other #200; end\n"
              "    join_none\n"
              "    #5 disable other;\n"
              "  end\n"
              "endmodule\n",
          f, "subclause_35_09_disable_a_sibling");
  EXPECT_EQ(g_return, 0);
  EXPECT_EQ(g_state, 0);
  EXPECT_EQ(ValueOf(f, "t"), 100U);
  EXPECT_EQ(FatalOf(f), "");
}

TEST(DpiDisableFromADesign, ADisabledChainInAProgramDisablesTheImport) {
  ResetC(1, false);
  SimFixture f;
  RunLong(std::string("program top;\n") + kLongExport +
              "  int t;\n"
              "  initial begin\n"
              "    fork begin : blk c_disabled(); end join_none\n"
              "    #5 disable blk;\n"
              "    t = $time;\n"
              "    #10;\n"
              "  end\n"
              "endprogram\n",
          f, "subclause_35_09_disable_in_a_program");
  EXPECT_EQ(g_return, 1);
  EXPECT_EQ(g_state, 1);
  EXPECT_EQ(ValueOf(f, "t"), 5U);
  EXPECT_EQ(FatalOf(f), "");
}

TEST(DpiDisableFromADesign, ADisabledChainInAClassMethodDisablesTheImport) {
  ResetC(1, false);
  SimFixture f;
  RunLong(std::string("module top;\n") + kLongExport +
              "  int t;\n"
              "  class C;\n"
              "    task go();\n"
              "      fork begin : blk c_disabled(); end join_none\n"
              "      #5 disable blk;\n"
              "      t = $time;\n"
              "    endtask\n"
              "  endclass\n"
              "  C c;\n"
              "  initial begin c = new; c.go(); end\n"
              "endmodule\n",
          f, "subclause_35_09_disable_in_a_method");
  EXPECT_EQ(g_return, 1);
  EXPECT_EQ(g_state, 1);
  EXPECT_EQ(ValueOf(f, "t"), 5U);
  EXPECT_EQ(FatalOf(f), "");
}

TEST(DpiDisableFromADesign,
     DISABLED_ADisabledChainInAPackageTaskDisablesTheImport) {
  ResetC(1, false);
  SimFixture f;
  RunLong(std::string("package p;\n") + kLongExport +
              "  task go(output int t);\n"
              "    fork begin : blk c_disabled(); end join_none\n"
              "    #5 disable blk;\n"
              "    t = $time;\n"
              "  endtask\n"
              "endpackage\n"
              "module top;\n"
              "  int t;\n"
              "  initial p::go(t);\n"
              "endmodule\n",
          f, "subclause_35_09_disable_in_a_package");
  EXPECT_EQ(g_return, 1);
  EXPECT_EQ(g_state, 1);
  EXPECT_EQ(ValueOf(f, "t"), 5U);
  EXPECT_EQ(FatalOf(f), "");
}

constexpr const char* kKillExport =
    "module top;\n"
    "  export \"DPI-C\" function sv_kill;\n"
    "  import \"DPI-C\" context function int c_kill();\n"
    "  function void sv_kill(); disable blk; endfunction\n"
    "  int r = 0;\n"
    "  int after = 0;\n"
    "  int later = 0;\n"
    "  initial begin : blk r = c_kill(); after = 1; end\n"
    "  initial #10 later = 1;\n"
    "endmodule\n";

void RunKill(SimFixture& f, const char* dir) {
  RunWithImportsBound(
      kKillExport, f,
      {{"c_kill", reinterpret_cast<void*>(&KillThroughAnExportedFunction)}},
      dir);
}

TEST(DpiDisableFromADesign,
     DISABLED_AnExportedFunctionReturnUnderADisableDisables) {
  ResetC(0, true);
  SimFixture f;
  RunKill(f, "subclause_35_09_disable_through_a_function");
  EXPECT_EQ(g_state, 1);
  EXPECT_EQ(ValueOf(f, "after"), 0U);
  EXPECT_EQ(ValueOf(f, "later"), 1U);
  EXPECT_EQ(FatalOf(f), "");
}

TEST(DpiDisableFromADesign,
     DISABLED_AnUnacknowledgedFunctionReturnUnderADisableIsFatal) {
  ResetC(0, false);
  SimFixture f;
  RunKill(f, "subclause_35_09_function_unacknowledged");
  EXPECT_EQ(g_state, 1);
  EXPECT_NE(FatalOf(f).find("35.9 item c)"), std::string::npos);
}

TEST(DpiDisableFromADesign, DISABLED_AnItemCFatalErrorEndsTheRun) {
  ResetC(0, false);
  SimFixture f;
  RunKill(f, "subclause_35_09_function_fatal_ends");
  EXPECT_NE(FatalOf(f).find("35.9 item c)"), std::string::npos);
  EXPECT_EQ(ValueOf(f, "later"), 0U);
}

TEST(DpiDisableFromADesign, AnImportCallingNoExportNeverEntersTheState) {
  ResetC(0, false);
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  import \"DPI-C\" context task c_probe();\n"
      "  int x = 0;\n"
      "  initial begin\n"
      "    fork begin : blk c_probe(); #10 x = 1; end join_none\n"
      "    #5 disable blk;\n"
      "  end\n"
      "endmodule\n",
      f, {{"c_probe", reinterpret_cast<void*>(&ReadTheStateOnly)}},
      "subclause_35_09_no_export_call");
  EXPECT_EQ(g_state, 0);
  EXPECT_EQ(ValueOf(f, "x"), 0U);
  EXPECT_EQ(FatalOf(f), "");
}

TEST(DpiDisableFromADesign, AnExportThatCompletesLeavesTheStateAtZero) {
  ResetC(0, false);
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  export \"DPI-C\" task sv_long;\n"
      "  import \"DPI-C\" context task c_disabled();\n"
      "  task sv_long(); #2; endtask\n"
      "  int t;\n"
      "  initial begin c_disabled(); t = $time; end\n"
      "endmodule\n",
      f, {{"c_disabled", reinterpret_cast<void*>(&CallTheLongExport)}},
      "subclause_35_09_export_completes");
  EXPECT_EQ(g_return, 0);
  EXPECT_EQ(g_state, 0);
  EXPECT_EQ(ValueOf(f, "t"), 2U);
  EXPECT_EQ(FatalOf(f), "");
}

TEST(DpiDisableFromADesign, ADisableOfTheExportedTaskLeavesItsImportAlone) {
  ResetC(0, false);
  SimFixture f;
  RunLong(std::string("module top;\n") + kLongExport +
              "  int after = 0;\n"
              "  int at = 0;\n"
              "  initial begin\n"
              "    fork begin c_disabled(); after = 1; at = $time; end "
              "join_none\n"
              "    #5 disable sv_long;\n"
              "  end\n"
              "endmodule\n",
          f, "subclause_35_09_disable_the_export");
  EXPECT_EQ(g_return, 0);
  EXPECT_EQ(g_state, 0);
  EXPECT_EQ(ValueOf(f, "after"), 1U);
  EXPECT_EQ(ValueOf(f, "at"), 5U);
  EXPECT_EQ(FatalOf(f), "");
}

constexpr const char* kDisabledBlock =
    "  int later = 0;\n"
    "  initial begin\n"
    "    fork begin : blk c_disabled(); end join_none\n"
    "    #5 disable blk;\n"
    "  end\n"
    "  initial #50 later = 1;\n"
    "endmodule\n";

TEST(DpiDisableFromADesign, AnImportedTaskGivingOneUnderADisableIsNotFatal) {
  ResetC(1, false);
  SimFixture f;
  RunLong(std::string("module top;\n") + kLongExport + kDisabledBlock, f,
          "subclause_35_09_task_gives_one");
  EXPECT_EQ(g_return, 1);
  EXPECT_EQ(FatalOf(f), "");
  EXPECT_EQ(ValueOf(f, "later"), 1U);
}

TEST(DpiDisableFromADesign,
     DISABLED_AnImportedTaskGivingZeroUnderADisableIsFatal) {
  ResetC(0, false);
  SimFixture f;
  RunLong(std::string("module top;\n") + kLongExport + kDisabledBlock, f,
          "subclause_35_09_task_gives_zero");
  EXPECT_EQ(g_return, 1);
  EXPECT_NE(FatalOf(f).find("35.9 item b)"), std::string::npos);
}

TEST(DpiDisableFromADesign, DISABLED_AnItemBFatalErrorEndsTheRun) {
  ResetC(0, false);
  SimFixture f;
  RunLong(std::string("module top;\n") + kLongExport + kDisabledBlock, f,
          "subclause_35_09_task_fatal_ends");
  EXPECT_NE(FatalOf(f).find("35.9 item b)"), std::string::npos);
  EXPECT_EQ(ValueOf(f, "later"), 0U);
}

TEST(DpiDisableFromADesign,
     DISABLED_AnImportedTaskGivingOneWithNoDisableIsFatal) {
  ResetC(1, false);
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  export \"DPI-C\" task sv_long;\n"
      "  import \"DPI-C\" context task c_disabled();\n"
      "  task sv_long(); #2; endtask\n"
      "  initial c_disabled();\n"
      "endmodule\n",
      f, {{"c_disabled", reinterpret_cast<void*>(&CallTheLongExport)}},
      "subclause_35_09_task_gives_one_undisabled");
  EXPECT_EQ(g_return, 0);
  EXPECT_NE(FatalOf(f).find("35.9 item b)"), std::string::npos);
}

constexpr const char* kSecondExport =
    "module top;\n"
    "  export \"DPI-C\" task sv_long;\n"
    "  export \"DPI-C\" task sv_second;\n"
    "  import \"DPI-C\" context task c_twice();\n"
    "  task sv_long(); #100; endtask\n"
    "  int n = 0;\n"
    "  task sv_second(); n = 1; endtask\n"
    "  int later = 0;\n"
    "  initial begin\n"
    "    fork begin : blk c_twice(); end join_none\n"
    "    #5 disable blk;\n"
    "  end\n"
    "  initial #50 later = 1;\n"
    "endmodule\n";

void RunTwice(SimFixture& f, const char* dir) {
  RunWithImportsBound(
      kSecondExport, f,
      {{"c_twice", reinterpret_cast<void*>(&CallASecondExportAfterTheDisable)}},
      dir);
}

TEST(DpiDisableFromADesign, AnExportCallAfterTheDisableIsRefusedAsFatal) {
  ResetC(1, false);
  SimFixture f;
  RunTwice(f, "subclause_35_09_second_export");
  EXPECT_EQ(g_return, 1);
  EXPECT_EQ(ValueOf(f, "n"), 0U);
  EXPECT_NE(FatalOf(f).find("35.9 item d)"), std::string::npos);
}

TEST(DpiDisableFromADesign, DISABLED_AnItemDFatalErrorEndsTheRun) {
  ResetC(1, false);
  SimFixture f;
  RunTwice(f, "subclause_35_09_second_export_ends");
  EXPECT_NE(FatalOf(f).find("35.9 item d)"), std::string::npos);
  EXPECT_EQ(ValueOf(f, "later"), 0U);
}

TEST(DpiDisableFromADesign, OutputsOfADisabledImportedTaskRaiseNoError) {
  ResetC(1, false);
  SimFixture f;
  RunWithImportsBound(
      std::string("module top;\n") +
          "  export \"DPI-C\" task sv_long;\n"
          "  import \"DPI-C\" context task c_out(output int o);\n"
          "  task sv_long(); #100; endtask\n"
          "  int v = 5;\n"
          "  int t;\n"
          "  initial begin\n"
          "    fork begin : blk c_out(v); end join_none\n"
          "    #5 disable blk;\n"
          "    t = $time;\n"
          "  end\n"
          "endmodule\n",
      f, {{"c_out", reinterpret_cast<void*>(&WriteThenWaitInTheExport)}},
      "subclause_35_09_disabled_outputs");
  EXPECT_EQ(g_return, 1);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(FatalOf(f), "");
  EXPECT_EQ(ValueOf(f, "t"), 5U);
}

TEST(DpiDisableFromADesign, ACallAfterTheDisabledChainWritesItsOutput) {
  ResetC(1, false);
  SimFixture f;
  RunWithImportsBound(
      std::string("module top;\n") +
          "  export \"DPI-C\" task sv_long;\n"
          "  import \"DPI-C\" context task c_out(output int o);\n"
          "  import \"DPI-C\" task c_nine(output int o);\n"
          "  task sv_long(); #100; endtask\n"
          "  int v = 5;\n"
          "  int w = 5;\n"
          "  initial begin\n"
          "    fork begin : blk c_out(v); end join_none\n"
          "    #5 disable blk;\n"
          "    #1 c_nine(w);\n"
          "  end\n"
          "endmodule\n",
      f,
      {{"c_out", reinterpret_cast<void*>(&WriteThenWaitInTheExport)},
       {"c_nine", reinterpret_cast<void*>(&WriteNine)}},
      "subclause_35_09_output_after_unwind");
  EXPECT_EQ(g_state, 1);
  EXPECT_EQ(ValueOf(f, "w"), 9U);
  EXPECT_EQ(FatalOf(f), "");
}

}  // namespace
