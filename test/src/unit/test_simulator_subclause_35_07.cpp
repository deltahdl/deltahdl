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

template <typename Function>
Function ExportNamed(const char* name) {
  return reinterpret_cast<Function>(dlsym(RTLD_DEFAULT, name));
}

int ExportPlusOne(const char* name, int a) {
  auto exported = ExportNamed<int (*)(int)>(name);
  return exported == nullptr ? -1 : exported(a) + 1;
}

int ViaExport(int a) { return ExportPlusOne("sv_double", a); }

int ViaPackageExport(int a) { return ExportPlusOne("pk_f", a); }

int ViaInterfaceExport(int a) { return ExportPlusOne("if_f", a); }

int ViaGenerateExport(int a) { return ExportPlusOne("g_f", a); }

int UnexportedHasNoSymbol() {
  return dlsym(RTLD_DEFAULT, "sv_never_exported_f") == nullptr ? 1 : 0;
}

int WhereAmI() {
  const char* name = svGetNameFromScope(svGetScope());
  if (name == nullptr) return 0;
  std::string_view path(name);
  if (path == "top.u1") return 1;
  if (path == "top.u2") return 2;
  return 9;
}

int WhereFromBothInstances() {
  auto sv_where = ExportNamed<int (*)()>("sv_where");
  if (sv_where == nullptr) return -1;
  svSetScope(svGetScopeFromName("top.u1"));
  int first = sv_where();
  svSetScope(svGetScopeFromName("top.u2"));
  int second = sv_where();
  return (first * 10) + second;
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

uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

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

TEST(DpiExportedFunctionInADesign, AnOutputFormalIsStillWrittenBack) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a;\n"
      "  function int f(input int x, output int o);\n"
      "    o = x * 3;\n"
      "    return x;\n"
      "  endfunction\n"
      "  export \"DPI-C\" function f;\n"
      "  initial void'(f(7, a));\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 21u);
}

TEST(DpiExportedFunctionInADesign, APackageCallIsUnchangedByTheExport) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "package pk;\n"
      "  function int f(input int x); return x + 100; endfunction\n"
      "  export \"DPI-C\" function f;\n"
      "endpackage\n"
      "module t;\n"
      "  int x;\n"
      "  initial x = pk::f(5);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 105u);
}

TEST(DpiExportedFunctionInADesign, AnInterfaceCallIsUnchangedByTheExport) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "interface i;\n"
      "  function int f(input int x); return x + 200; endfunction\n"
      "  export \"DPI-C\" function f;\n"
      "endinterface\n"
      "module t;\n"
      "  i u();\n"
      "  int x;\n"
      "  initial x = u.f(5);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 205u);
}

TEST(DpiExportCalledFromC, AFunctionWithoutAnExportHasNoSymbol) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  function int sv_never_exported_f(); return 5; endfunction\n"
      "  import \"DPI-C\" context function int probe();\n"
      "  int r;\n"
      "  initial r = probe();\n"
      "endmodule\n",
      f, {{"probe", reinterpret_cast<void*>(&UnexportedHasNoSymbol)}},
      "subclause_35_07_no_export");
  EXPECT_EQ(VariableValue(f, "r"), 1U);
}

TEST(DpiExportCalledFromC, DISABLED_APackageExportIsCalledFromC) {
  SimFixture f;
  RunWithImportsBound(
      "package pk;\n"
      "  export \"DPI-C\" function pk_f;\n"
      "  import \"DPI-C\" context function int call_pk(input int a);\n"
      "  function int pk_f(input int a); return a + 100; endfunction\n"
      "endpackage\n"
      "module top;\n"
      "  int r;\n"
      "  initial r = pk::call_pk(5);\n"
      "endmodule\n",
      f, {{"call_pk", reinterpret_cast<void*>(&ViaPackageExport)}},
      "subclause_35_07_package_export");
  EXPECT_EQ(VariableValue(f, "r"), 106U);
}

TEST(DpiExportCalledFromC, DISABLED_AnInterfaceInstanceExportIsCalledFromC) {
  SimFixture f;
  RunWithImportsBound(
      "interface i;\n"
      "  export \"DPI-C\" function if_f;\n"
      "  import \"DPI-C\" context function int call_if(input int a);\n"
      "  function int if_f(input int a); return a + 200; endfunction\n"
      "  int r;\n"
      "  initial r = call_if(5);\n"
      "endinterface\n"
      "module top;\n"
      "  i u();\n"
      "endmodule\n",
      f, {{"call_if", reinterpret_cast<void*>(&ViaInterfaceExport)}},
      "subclause_35_07_interface_export");
  EXPECT_EQ(VariableValue(f, "u.r"), 206U);
}

TEST(DpiExportCalledFromC, AGenerateBlockExportIsCalledFromC) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  int r;\n"
      "  if (1) begin : g\n"
      "    export \"DPI-C\" function g_f;\n"
      "    import \"DPI-C\" context function int call_g(input int a);\n"
      "    function int g_f(input int a); return a + 300; endfunction\n"
      "    initial r = call_g(5);\n"
      "  end\n"
      "endmodule\n",
      f, {{"call_g", reinterpret_cast<void*>(&ViaGenerateExport)}},
      "subclause_35_07_generate_export");
  EXPECT_EQ(VariableValue(f, "r"), 306U);
}

TEST(DpiExportCalledFromC, AnExportRunsInTheContextOfItsInstance) {
  SimFixture f;
  RunWithImportsBound(
      "module m;\n"
      "  export \"DPI-C\" function sv_where;\n"
      "  import \"DPI-C\" context function int where_am_i();\n"
      "  function int sv_where(); return where_am_i(); endfunction\n"
      "endmodule\n"
      "module top;\n"
      "  import \"DPI-C\" context function int both();\n"
      "  m u1();\n"
      "  m u2();\n"
      "  int r;\n"
      "  initial r = both();\n"
      "endmodule\n",
      f,
      {{"both", reinterpret_cast<void*>(&WhereFromBothInstances)},
       {"where_am_i", reinterpret_cast<void*>(&WhereAmI)}},
      "subclause_35_07_export_context");
  EXPECT_EQ(VariableValue(f, "r"), 12U);
}

}  // namespace
