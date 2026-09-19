#include <gtest/gtest.h>

#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

// Annex H.6.5 (Context and noncontext tasks and functions), beside §35.5.3:
// an import's calls are instrumented to know their context only where the
// import is declared context; an export called from an import has the
// context the import set with svSetScope, or otherwise the instantiated
// scope where the import declaration is; a noncontext import shall not
// access any SystemVerilog data object other than its actual arguments and
// its call is no barrier to compiler optimizations, where a context import
// can access any data object through the VPI or an embedded export and its
// call is such a barrier; and only a context import's calls are properly
// instrumented, so only it can safely call functions of other APIs, the
// VPI and exported subroutines included. The cases check what an import may
// access, which import may safely call other APIs and that the runtime
// permits an export call to the one and refuses it to the other, which
// import's call is an optimization barrier, and that an export called from
// an import has the import's instantiated scope for context unless the
// import set another.

namespace {

DpiRtFunction Import(const char* name, bool is_context) {
  DpiRtFunction func;
  func.c_name = name;
  func.sv_name = name;
  func.return_type = DataTypeKind::kInt;
  func.is_context = is_context;
  return func;
}

// §H.6.5: a noncontext import shall access nothing of SystemVerilog beyond
// its actual arguments; a context import can access any data object.
TEST(DpiContextCalls, ANoncontextImportAccessesItsActualsAlone) {
  EXPECT_EQ(DpiAccessOfImport(false), DpiImportAccess::kActualArgumentsOnly);
  EXPECT_EQ(DpiAccessOfImport(true), DpiImportAccess::kAnyDataObject);
}

// §H.6.5: only a context import's calls are instrumented, so only it can
// safely call the VPI or an exported subroutine -- and the runtime lets a
// context import call an export where a noncontext one is refused.
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

// §H.6.5: a noncontext import's call shall not block compiler
// optimizations, affecting only its actual arguments; a context import's
// call is a barrier to them.
TEST(DpiContextCalls, ANoncontextCallIsNoBarrierToOptimizations) {
  EXPECT_FALSE(DpiImportCallIsOptimizationBarrier(false));
  EXPECT_TRUE(DpiImportCallIsOptimizationBarrier(true));

  DpiRuntime rt;
  rt.RegisterImport(Import("plain", false));
  rt.RegisterImport(Import("ctx", true));
  EXPECT_FALSE(rt.IsImportCallOptimizationBarrier("plain"));
  EXPECT_TRUE(rt.IsImportCallOptimizationBarrier("ctx"));
}

// §H.6.5: an export called from a context import has for context the
// instantiated scope where the import declaration is, unless the import
// invoked svSetScope before the call, which sets the context explicitly.
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
