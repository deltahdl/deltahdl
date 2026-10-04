#include <dlfcn.h>
#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "helpers_reported_error.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

// §35.7: the exports a registry answers for are the ones some declaration
// gave it. DpiRuntime.RegisterExportAndCall below makes the positive claim --
// a registered name is found and its body runs; this one makes the negative,
// which no other case states: a name no export declaration gave is not an
// export of the design, however many others were registered.
TEST(DpiRuntime, HasExportIsFalseForAnUndeclaredName) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_callback";
  exp.sv_name = "sv_callback";
  rt.RegisterExport(exp);

  EXPECT_FALSE(rt.HasExport("missing"));
}

TEST(DpiRuntime, RegisterExportAndCall) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_callback";
  exp.sv_name = "sv_callback";
  exp.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() * 2);
  };
  rt.RegisterExport(exp);

  EXPECT_EQ(rt.ExportCount(), 1u);
  EXPECT_TRUE(rt.HasExport("sv_callback"));

  auto result = rt.CallExport("sv_callback", {DpiArgValue::FromInt(21)});
  EXPECT_EQ(result.AsInt(), 42);
}

TEST(DpiRuntime, CallMissingExportReturnsZero) {
  DpiRuntime rt;
  auto result = rt.CallExport("nonexistent", {});
  EXPECT_EQ(result.AsInt(), 0);
}

// §35.7: every export declaration designates a context function. The runtime
// records that property unconditionally at registration, so a caller that
// passes is_context=false still ends up with a context export.
TEST(DpiRuntime, RegisteredExportIsAlwaysContext) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_callback";
  exp.sv_name = "sv_callback";
  exp.is_context = false;
  rt.RegisterExport(exp);

  const auto* stored = rt.FindExport("sv_callback");
  ASSERT_NE(stored, nullptr);
  EXPECT_TRUE(stored->is_context);
}

// §35.7: "Declaring a SystemVerilog function to be exported does not change its
// semantics or behavior from the SystemVerilog perspective; there is no effect
// on SystemVerilog usage other than making it possible for foreign language
// tasks and functions in a DPI call-chain to call the exported function." So a
// SystemVerilog call to an exported function returns what the function returns,
// exactly as it would without the export declaration.
TEST(DpiExportedFunctionInADesign, ACallToAnExportedFunctionReturnsItsResult) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  function int five();\n"
      "    return 5;\n"
      "  endfunction\n"
      "  export \"DPI-C\" function five;\n"
      "  initial x = five();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// The same rule holds of the arguments a call passes: exporting the function
// leaves the actual reaching the formal and the result computed from it. Five
// is what the case above returns from a body that reads nothing, so this one
// varies the actual to keep the answer out of the body.
TEST(DpiExportedFunctionInADesign, AnExportedFunctionStillReadsItsArguments) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  function int twice(input int v);\n"
      "    return v + v;\n"
      "  endfunction\n"
      "  export \"DPI-C\" function twice;\n"
      "  initial x = twice(21);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// The C functions the designs below import, each calling an export the way C
// code in a loaded library does: by its linkage name, found among the
// process's global symbols, where the forwarders deltahdl generates for a
// design's exports stand (§35.7, §H.8.2).
template <typename Function>
Function ExportNamed(const char* name) {
  return reinterpret_cast<Function>(dlsym(RTLD_DEFAULT, name));
}

int ViaExport(int a) {
  auto sv_double = ExportNamed<int (*)(int)>("sv_double");
  return sv_double == nullptr ? -1 : sv_double(a) + 1;
}

int ViaRenamedExport(int a) {
  auto f_plus = ExportNamed<int (*)(int)>("f_plus");
  return f_plus == nullptr ? -1 : f_plus(a) + 1000;
}

int DriveOutputs() {
  auto fill = ExportNamed<unsigned char (*)(int, int*)>("exported_sv_func");
  if (fill == nullptr) return -1;
  int table[8] = {};
  unsigned char bit = fill(3, table);
  return (table[0] * 100) + (table[7] * 10) + bit;
}

int TaskFromFunction() {
  auto sv_t = ExportNamed<int (*)()>("sv_t");
  return sv_t == nullptr ? -1 : sv_t();
}

int IdOf(const char* path) {
  auto sv_id = ExportNamed<int (*)()>("sv_id");
  svScope scope = svGetScopeFromName(path);
  if (sv_id == nullptr || scope == nullptr) return -1;
  svSetScope(scope);
  return sv_id();
}

// The value the design's variable `name` holds once the run is over, all ones
// where the run holds no such variable.
uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

// §35.7 with §35.5.3: a context import calls an exported function declared in
// its own scope, by the export's name, with the C prototype §H.8.2 gives it.
TEST(DpiExportCalledFromC, AContextImportCallsAnExportedFunction) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  export \"DPI-C\" function sv_double;\n"
      "  import \"DPI-C\" context function int via_export(input int a);\n"
      "  function int sv_double(input int a); return a * 2; endfunction\n"
      "  int r;\n"
      "  initial r = via_export(30);\n"
      "endmodule\n",
      f, {{"via_export", reinterpret_cast<void*>(&ViaExport)}},
      "subclause_35_07_export_call");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "r"), 61U);
}

// §35.4 with §35.7: a c_identifier gives an export its linkage name, an
// escaped identifier's export included.
TEST(DpiExportCalledFromC, AnExportIsCalledByItsCIdentifier) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  export \"DPI-C\" f_plus = function \\f+ ;\n"
      "  import \"DPI-C\" context c_name = function int sv_name(input int a);\n"
      "  function int \\f+ (input int a); return a + 1; endfunction\n"
      "  int r;\n"
      "  initial r = sv_name(7);\n"
      "endmodule\n",
      f, {{"c_name", reinterpret_cast<void*>(&ViaRenamedExport)}},
      "subclause_35_07_export_c_identifier");
  EXPECT_EQ(VariableValue(f, "r"), 1008U);
}

// §H.8.2 with §H.10.2: an exported function called from C returns a bit by
// value and fills an unpacked int output array through the pointer C passes.
TEST(DpiExportCalledFromC, AnExportFillsAnOutputArray) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  export \"DPI-C\" function exported_sv_func;\n"
      "  import \"DPI-C\" context function int drive();\n"
      "  function bit exported_sv_func(input int i, output int o [0:7]);\n"
      "    foreach (o[k]) o[k] = i + k;\n"
      "    return 1'b1;\n"
      "  endfunction\n"
      "  int r;\n"
      "  initial r = drive();\n"
      "endmodule\n",
      f, {{"drive", reinterpret_cast<void*>(&DriveOutputs)}},
      "subclause_35_07_export_output");
  EXPECT_EQ(VariableValue(f, "r"), 401U);
}

// §35.8: an exported task may never be enabled from an imported function,
// and the attempt is reported.
TEST(DpiExportCalledFromC, AnExportedTaskFromAnImportedFunctionIsAnError) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  export \"DPI-C\" task sv_t;\n"
      "  import \"DPI-C\" context function int c_fn();\n"
      "  task sv_t(); #1; endtask\n"
      "  int r;\n"
      "  initial r = c_fn();\n"
      "endmodule\n",
      f, {{"c_fn", reinterpret_cast<void*>(&TaskFromFunction)}},
      "subclause_35_07_export_task_from_function");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "exported task 'sv_t' enabled from imported "
                            "function 'c_fn'",
                            0, "35.8"));
}

// §35.5.3 with §H.9.3: svGetScopeFromName and svSetScope select the
// instance whose export a call reaches.
TEST(DpiExportCalledFromC, TheScopeSelectsTheInstancesExport) {
  SimFixture f;
  RunWithImportsBound(
      "module m #(int ID);\n"
      "  export \"DPI-C\" function sv_id;\n"
      "  function int sv_id(); return ID; endfunction\n"
      "endmodule\n"
      "module top;\n"
      "  import \"DPI-C\" context function int id_of(input string path);\n"
      "  m #(4) u1();\n"
      "  m #(8) u2();\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = id_of(\"top.u1\");\n"
      "    b = id_of(\"top.u2\");\n"
      "  end\n"
      "endmodule\n",
      f, {{"id_of", reinterpret_cast<void*>(&IdOf)}},
      "subclause_35_07_export_scope");
  EXPECT_EQ(VariableValue(f, "a"), 4U);
  EXPECT_EQ(VariableValue(f, "b"), 8U);
}

}  // namespace
