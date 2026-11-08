#include <gtest/gtest.h>

#include <vector>

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

}  // namespace
