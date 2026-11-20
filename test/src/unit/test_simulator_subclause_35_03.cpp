#include <dlfcn.h>
#include <gtest/gtest.h>

#include <cstdint>
#include <map>
#include <memory>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiTwoLayers, SvLayerCallsForeignImplBySvName) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_add_one";
  func.sv_name = "sv_add_one";
  func.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() + 1);
  };
  rt.RegisterImport(func);

  const DpiArgValue kResult =
      rt.CallImport("sv_add_one", {DpiArgValue::FromInt(41)});
  EXPECT_EQ(kResult.AsInt(), 42);
}

TEST(DpiTwoLayers, ForeignImplIsOpaqueToSvLayer) {
  DpiRuntime rt_a;
  DpiRtFunction direct;
  direct.c_name = "c_double_direct";
  direct.sv_name = "sv_double";
  direct.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() * 2);
  };
  rt_a.RegisterImport(direct);

  DpiRuntime rt_b;
  DpiRtFunction by_addition;
  by_addition.c_name = "c_double_by_addition";
  by_addition.sv_name = "sv_double";
  by_addition.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    const int32_t kX = args[0].AsInt();
    return DpiArgValue::FromInt(kX + kX);
  };
  rt_b.RegisterImport(by_addition);

  const std::vector<DpiArgValue> kActual = {DpiArgValue::FromInt(21)};
  EXPECT_EQ(rt_a.CallImport("sv_double", kActual).AsInt(),
            rt_b.CallImport("sv_double", kActual).AsInt());
}

TEST(DpiTwoLayers, SvLayerResolvesBySvNameNotForeignSymbol) {
  DpiRuntime rt;
  DpiRtFunction lo;
  lo.c_name = "c_shared";
  lo.sv_name = "sv_lo";
  lo.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(1);
  };
  rt.RegisterImport(lo);

  DpiRtFunction hi;
  hi.c_name = "c_shared";
  hi.sv_name = "sv_hi";
  hi.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(2);
  };
  rt.RegisterImport(hi);

  EXPECT_EQ(rt.CallImport("sv_lo", {}).AsInt(), 1);
  EXPECT_EQ(rt.CallImport("sv_hi", {}).AsInt(), 2);
}

TEST(DpiTwoLayers, ForeignInternalStateIsOpaqueToSvLayer) {
  DpiRuntime rt;
  DpiRtFunction counter;
  counter.c_name = "c_next";
  counter.sv_name = "sv_next";
  auto ticks = std::make_shared<int32_t>(0);
  counter.impl = [ticks](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(++(*ticks));
  };
  rt.RegisterImport(counter);

  EXPECT_EQ(rt.CallImport("sv_next", {}).AsInt(), 1);
  EXPECT_EQ(rt.CallImport("sv_next", {}).AsInt(), 2);
  EXPECT_EQ(rt.CallImport("sv_next", {}).AsInt(), 3);
}

TEST(DpiTwoLayers, ExportedSvBodyIsUnchangedByWhichForeignEntryCallsIt) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_scale";
  exp.sv_name = "sv_scale";
  exp.return_type = DataTypeKind::kInt;
  exp.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  exp.impl = [](const std::vector<DpiArgValue>& args) {
    return DpiArgValue::FromInt(args[0].AsInt() * 3);
  };
  rt.RegisterExport(exp);

  const DpiArgValue kDirect =
      rt.CallExport("sv_scale", {DpiArgValue::FromInt(14)});

  DpiScope scope;
  scope.name = "top";
  rt.EnterContextImportCall("ctx_import", scope);
  DpiArgValue from_import;
  rt.CallExportFromImport("sv_scale", {DpiArgValue::FromInt(14)}, &from_import);

  EXPECT_EQ(kDirect.AsInt(), 42);
  EXPECT_EQ(from_import.AsInt(), 42);
}

int SubtractTwo(int a) { return a - 2; }

std::map<std::string, void*> SubtractTwoBound() {
  return {{"subtract_two", reinterpret_cast<void*>(&SubtractTwo)}};
}

constexpr const char* kSubtractTwoImport =
    "  import \"DPI-C\" function int subtract_two(input int a);\n";

uint64_t ValueOfRAfter(const std::string& src,
                       const std::map<std::string, void*>& functions,
                       const char* dir, const char* r = "r") {
  SimFixture f;
  RunWithImportsBound(src, f, functions, std::string("subclause_35_03_") + dir);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  auto* var = f.ctx.FindVariable(r);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

TEST(DpiCLinkage, APackageImportCallReachesItsCSymbol) {
  EXPECT_EQ(ValueOfRAfter(std::string("package pk;\n") + kSubtractTwoImport +
                              "endpackage\n"
                              "module t;\n"
                              "  import pk::*;\n"
                              "  int r;\n"
                              "  initial r = subtract_two(50);\n"
                              "endmodule\n",
                          SubtractTwoBound(), "package"),
            48U);
}

TEST(DpiCLinkage, AUnitImportCallReachesItsCSymbol) {
  EXPECT_EQ(ValueOfRAfter(std::string(kSubtractTwoImport) +
                              "module t;\n"
                              "  int r;\n"
                              "  initial r = subtract_two(60);\n"
                              "endmodule\n",
                          SubtractTwoBound(), "unit"),
            58U);
}

TEST(DpiCLinkage, ANonTopInstancesImportCallReachesItsCSymbol) {
  EXPECT_EQ(ValueOfRAfter(std::string("module child;\n") + kSubtractTwoImport +
                              "  int r;\n"
                              "  initial r = subtract_two(70);\n"
                              "endmodule\n"
                              "module t;\n"
                              "  child c();\n"
                              "endmodule\n",
                          SubtractTwoBound(), "non_top", "c.r"),
            68U);
}

const char* export_to_call = "";

int CallsTheExport(int a) {
  auto exported =
      reinterpret_cast<int (*)(int)>(dlsym(RTLD_DEFAULT, export_to_call));
  return exported == nullptr ? -1 : exported(a) + 1;
}

std::string ExportAndCaller(const char* name) {
  export_to_call = name;
  return std::string("  export \"DPI-C\" ") + name +
         " = function triple;\n"
         "  function int triple(input int a); return a * 3; endfunction\n"
         "  import \"DPI-C\" context function int calls_the_export("
         "input int a);\n";
}

uint64_t ValueAfterCallingTheExport(const std::string& src, const char* dir,
                                    const char* r) {
  return ValueOfRAfter(
      src, {{"calls_the_export", reinterpret_cast<void*>(&CallsTheExport)}},
      dir, r);
}

TEST(DpiCLinkage, AModuleExportIsCalledFromC) {
  EXPECT_EQ(
      ValueAfterCallingTheExport("module t;\n" + ExportAndCaller("triple_mod") +
                                     "  int r;\n"
                                     "  initial r = calls_the_export(4);\n"
                                     "endmodule\n",
                                 "module_export", "r"),
      13U);
}

TEST(DpiCLinkage, DISABLED_APackageExportIsCalledFromC) {
  EXPECT_EQ(ValueAfterCallingTheExport(
                "package pk;\n" + ExportAndCaller("triple_pk") +
                    "endpackage\n"
                    "module t;\n"
                    "  int r;\n"
                    "  initial r = pk::calls_the_export(5);\n"
                    "endmodule\n",
                "package_export", "r"),
            16U);
}

TEST(DpiCLinkage, DISABLED_AnInterfaceExportIsCalledFromC) {
  EXPECT_EQ(ValueAfterCallingTheExport(
                "interface ifc;\n" + ExportAndCaller("triple_ifc") +
                    "  int r;\n"
                    "  initial r = calls_the_export(6);\n"
                    "endinterface\n"
                    "module t;\n"
                    "  ifc i();\n"
                    "endmodule\n",
                "interface_export", "i.r"),
            19U);
}

TEST(DpiCLinkage, DISABLED_AProgramExportIsCalledFromC) {
  EXPECT_EQ(ValueAfterCallingTheExport(
                "program pr;\n" + ExportAndCaller("triple_pr") +
                    "  int r;\n"
                    "  initial r = calls_the_export(7);\n"
                    "endprogram\n"
                    "module t;\n"
                    "  pr p();\n"
                    "endmodule\n",
                "program_export", "p.r"),
            22U);
}

}  // namespace
