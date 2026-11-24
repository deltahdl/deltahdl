#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

DpiRtFunction Import(const char* name, bool is_context) {
  DpiRtFunction func;
  func.c_name = name;
  func.sv_name = name;
  func.return_type = DataTypeKind::kInt;
  func.is_context = is_context;
  return func;
}

TEST(DpiContextCalls, ANoncontextImportAccessesItsActualsAlone) {
  EXPECT_EQ(DpiAccessOfImport(false), DpiImportAccess::kActualArgumentsOnly);
  EXPECT_EQ(DpiAccessOfImport(true), DpiImportAccess::kAnyDataObject);
}

TEST(DpiContextCalls, OnlyAContextImportMaySafelyCallOtherApis) {
  EXPECT_TRUE(DpiImportMaySafelyCallOtherApis(true));
  EXPECT_FALSE(DpiImportMaySafelyCallOtherApis(false));

  DpiRuntime rt;
  DpiRtExport exp;
  exp.sv_name = "sv_export";
  exp.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(5);
  };
  rt.RegisterExport(exp);
  DpiArgValue result;
  rt.EnterNoncontextImportCall("plain");
  EXPECT_EQ(rt.CallExportFromImport("sv_export", {}, &result),
            DpiExportCallStatus::kNoncontextChain);
  rt.LeaveImportCall();
  DpiScope scope;
  scope.name = "top.u1";
  rt.EnterContextImportCall("ctx", scope);
  EXPECT_EQ(rt.CallExportFromImport("sv_export", {}, &result),
            DpiExportCallStatus::kOk);
  EXPECT_EQ(result.AsInt(), 5);
}

TEST(DpiContextCalls, ANoncontextCallIsNoBarrierToOptimizations) {
  EXPECT_FALSE(DpiImportCallIsOptimizationBarrier(false));
  EXPECT_TRUE(DpiImportCallIsOptimizationBarrier(true));

  DpiRuntime rt;
  rt.RegisterImport(Import("plain", false));
  rt.RegisterImport(Import("ctx", true));
  EXPECT_FALSE(rt.IsImportCallOptimizationBarrier("plain"));
  EXPECT_TRUE(rt.IsImportCallOptimizationBarrier("ctx"));
}

TEST(DpiContextCalls, AnExportsContextIsTheImportsScopeUnlessSet) {
  DpiRuntime rt;
  DpiScope decl_scope;
  decl_scope.name = "top.u1";
  rt.EnterContextImportCall("ctx", decl_scope);
  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.u1");
  DpiScope other;
  other.name = "top.u2";
  rt.SetScope(&other);
  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.u2");
}

int CallMark() {
  auto mark = NamedExport<int (*)()>("sv_mark");
  if (mark != nullptr) mark();
  return 0;
}

void RunNoncontext(const std::string& import, const std::string& call,
                   SimFixture& f) {
  RunWithImportsBound("module t;\n  int marked = 3;\n  import \"DPI-C\" " +
                          import +
                          ";\n"
                          "  initial " +
                          call + ";\nendmodule\n",
                      f, {{"call_mark", reinterpret_cast<void*>(&CallMark)}},
                      "annex_h_06_05_noncontext");
}

const char* const kMarkFunction =
    "; export \"DPI-C\" function sv_mark; function int sv_mark(); marked = 8; "
    "return 0; endfunction";

const char* const kMarkTask =
    "; export \"DPI-C\" task sv_mark; task sv_mark(); marked = 8; endtask";

const char* const kNotContext =
    "exported subroutine 'sv_mark' called from imported subroutine "
    "'call_mark', which is not declared context";

TEST(DpiContextCalls, AnExportCalledFromAPlainImportIsReported) {
  SimFixture f;
  RunNoncontext(std::string("function int call_mark()") + kMarkFunction,
                "void'(call_mark())", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNotContext, 0, "35.5.3"));
  EXPECT_EQ(DesignValue(f, "marked"), 3U);
}

TEST(DpiContextCalls, AnExportCalledFromAPureImportIsReported) {
  SimFixture f;
  RunNoncontext(std::string("pure function int call_mark()") + kMarkFunction,
                "void'(call_mark())", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNotContext, 0, "35.5.3"));
  EXPECT_EQ(DesignValue(f, "marked"), 3U);
}

TEST(DpiContextCalls, AnExportedTaskCalledFromAPlainImportedTaskIsReported) {
  SimFixture f;
  RunNoncontext(std::string("task call_mark()") + kMarkTask, "call_mark()", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNotContext, 0, "35.5.3"));
  EXPECT_EQ(DesignValue(f, "marked"), 3U);
}

TEST(DpiContextCalls, AnExportCalledFromAContextImportRuns) {
  SimFixture f;
  RunNoncontext(std::string("context function int call_mark()") + kMarkFunction,
                "void'(call_mark())", f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(DesignValue(f, "marked"), 8U);
  SimFixture g;
  RunNoncontext(std::string("context task call_mark()") + kMarkTask,
                "call_mark()", g);
  EXPECT_TRUE(g.diag.Diagnostics().empty());
  EXPECT_EQ(DesignValue(g, "marked"), 8U);
}

int IdOfCaller() {
  auto sv_id = NamedExport<int (*)()>("sv_id");
  return sv_id == nullptr ? -1 : sv_id();
}

TEST(DpiContextCalls, EachInstancesImportReachesItsOwnInstancesExport) {
  SimFixture f;
  RunWithImportsBound(
      "module m #(int ID);\n"
      "  import \"DPI-C\" context function int call_back();\n"
      "  export \"DPI-C\" function sv_id;\n"
      "  function int sv_id(); return ID; endfunction\n"
      "  int r;\n"
      "  initial r = call_back();\n"
      "endmodule\n"
      "module top;\n"
      "  m #(4) u1();\n"
      "  m #(8) u2();\n"
      "endmodule\n",
      f, {{"call_back", reinterpret_cast<void*>(&IdOfCaller)}},
      "annex_h_06_05_instances");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(DesignValue(f, "u1.r"), 4U);
  EXPECT_EQ(DesignValue(f, "u2.r"), 8U);
}

int ReadThroughExport() {
  auto sv_read = NamedExport<int (*)()>("sv_read");
  return sv_read == nullptr ? -1 : sv_read();
}

TEST(DpiContextCalls, AContextImportSeesTheWriteBeforeItsCall) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" context function int read_back();\n"
      "  export \"DPI-C\" function sv_read;\n"
      "  int a = 5;\n"
      "  function int sv_read(); return a; endfunction\n"
      "  int first, second;\n"
      "  initial begin\n"
      "    a = 42;\n"
      "    first = read_back();\n"
      "    a = 43;\n"
      "    second = read_back();\n"
      "  end\n"
      "endmodule\n",
      f, {{"read_back", reinterpret_cast<void*>(&ReadThroughExport)}},
      "annex_h_06_05_barrier");
  EXPECT_EQ(DesignValue(f, "first"), 42U);
  EXPECT_EQ(DesignValue(f, "second"), 43U);
}

}  // namespace
