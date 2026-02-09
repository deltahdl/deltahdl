#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulation/dpi_runtime.h"

using namespace delta;

// =============================================================================
// DpiArgValue: typed argument construction and access
// =============================================================================

TEST(DpiRuntime, ArgValueInt) {
  auto v = DpiArgValue::FromInt(42);
  EXPECT_EQ(v.type, DataTypeKind::kInt);
  EXPECT_EQ(v.AsInt(), 42);
}

TEST(DpiRuntime, ArgValueLongint) {
  auto v = DpiArgValue::FromLongint(0x1'0000'0000LL);
  EXPECT_EQ(v.type, DataTypeKind::kLongint);
  EXPECT_EQ(v.AsLongint(), 0x1'0000'0000LL);
}

TEST(DpiRuntime, ArgValueReal) {
  auto v = DpiArgValue::FromReal(3.14);
  EXPECT_EQ(v.type, DataTypeKind::kReal);
  EXPECT_DOUBLE_EQ(v.AsReal(), 3.14);
}

TEST(DpiRuntime, ArgValueString) {
  auto v = DpiArgValue::FromString("hello");
  EXPECT_EQ(v.type, DataTypeKind::kString);
  EXPECT_EQ(v.AsString(), "hello");
}

TEST(DpiRuntime, ArgValueChandle) {
  int dummy = 0;
  auto v = DpiArgValue::FromChandle(&dummy);
  EXPECT_EQ(v.type, DataTypeKind::kChandle);
  EXPECT_EQ(v.AsChandle(), &dummy);
}

TEST(DpiRuntime, ArgValueBit) {
  auto v = DpiArgValue::FromBit(1);
  EXPECT_EQ(v.type, DataTypeKind::kBit);
  EXPECT_EQ(v.AsBit(), 1);
}

TEST(DpiRuntime, ArgValueLogic) {
  auto v = DpiArgValue::FromLogic(0);
  EXPECT_EQ(v.type, DataTypeKind::kLogic);
  EXPECT_EQ(v.AsLogic(), 0);
}

// =============================================================================
// DpiRuntime: import registration and invocation
// =============================================================================

TEST(DpiRuntime, RegisterImportAndCall) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_add";
  func.sv_name = "sv_add";
  func.return_type = DataTypeKind::kInt;
  func.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() + args[1].AsInt());
  };
  rt.RegisterImport(func);

  EXPECT_EQ(rt.ImportCount(), 1u);
  EXPECT_TRUE(rt.HasImport("sv_add"));
  EXPECT_FALSE(rt.HasImport("missing"));

  auto result = rt.CallImport(
      "sv_add", {DpiArgValue::FromInt(10), DpiArgValue::FromInt(20)});
  EXPECT_EQ(result.AsInt(), 30);
}

TEST(DpiRuntime, CallMissingImportReturnsZero) {
  DpiRuntime rt;
  auto result = rt.CallImport("nonexistent", {});
  EXPECT_EQ(result.AsInt(), 0);
}

TEST(DpiRuntime, ImportWithRealArgs) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_mul_real";
  func.sv_name = "sv_mul_real";
  func.return_type = DataTypeKind::kReal;
  func.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromReal(args[0].AsReal() * args[1].AsReal());
  };
  rt.RegisterImport(func);

  auto result = rt.CallImport(
      "sv_mul_real", {DpiArgValue::FromReal(2.5), DpiArgValue::FromReal(4.0)});
  EXPECT_DOUBLE_EQ(result.AsReal(), 10.0);
}

TEST(DpiRuntime, ImportWithStringArg) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_strlen";
  func.sv_name = "sv_strlen";
  func.return_type = DataTypeKind::kInt;
  func.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(
        static_cast<int32_t>(args[0].AsString().size()));
  };
  rt.RegisterImport(func);

  auto result = rt.CallImport("sv_strlen", {DpiArgValue::FromString("hello")});
  EXPECT_EQ(result.AsInt(), 5);
}

TEST(DpiRuntime, ImportWithChandleArg) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_identity";
  func.sv_name = "sv_identity";
  func.return_type = DataTypeKind::kChandle;
  func.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromChandle(args[0].AsChandle());
  };
  rt.RegisterImport(func);

  int dummy = 42;
  auto result =
      rt.CallImport("sv_identity", {DpiArgValue::FromChandle(&dummy)});
  EXPECT_EQ(result.AsChandle(), &dummy);
}

// =============================================================================
// DpiRuntime: export registration and invocation
// =============================================================================

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

// =============================================================================
// svdpi.h type mapping (S35.5)
// =============================================================================

TEST(DpiRuntime, SvBitVecValSize) { EXPECT_EQ(sizeof(svBitVecVal), 4u); }

TEST(DpiRuntime, SvLogicVecValLayout) {
  svLogicVecVal v;
  v.aval = 0xDEADBEEF;
  v.bval = 0;
  EXPECT_EQ(v.aval, 0xDEADBEEFu);
  EXPECT_TRUE(v.bval == 0);  // Known value.
}

// =============================================================================
// DpiRuntime: scope management (svGetScope, svSetScope)
// =============================================================================

TEST(DpiRuntime, ScopeManagement) {
  DpiRuntime rt;
  EXPECT_EQ(rt.CurrentScope(), nullptr);

  DpiScope scope;
  scope.name = "top.dut";
  scope.module_name = "dut";
  rt.PushScope(scope);
  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.dut");

  DpiScope inner;
  inner.name = "top.dut.sub";
  inner.module_name = "sub";
  rt.PushScope(inner);
  EXPECT_EQ(rt.CurrentScope()->name, "top.dut.sub");

  rt.PopScope();
  ASSERT_NE(rt.CurrentScope(), nullptr);
  EXPECT_EQ(rt.CurrentScope()->name, "top.dut");

  rt.PopScope();
  EXPECT_EQ(rt.CurrentScope(), nullptr);
}

TEST(DpiRuntime, SetAndGetScope) {
  DpiRuntime rt;
  DpiScope scope;
  scope.name = "top.mod";
  rt.PushScope(scope);

  const DpiScope* saved = rt.GetScope();
  ASSERT_NE(saved, nullptr);

  rt.PopScope();
  EXPECT_EQ(rt.CurrentScope(), nullptr);

  // Restore scope.
  rt.SetScope(saved);
  EXPECT_EQ(rt.GetScope(), saved);
}

// =============================================================================
// DpiRuntime: open array support (S35.5.6)
// =============================================================================

TEST(DpiRuntime, OpenArrayHandleOperations) {
  svOpenArrayHandle h;
  h.data = nullptr;
  h.size = 10;
  h.elem_width = 32;

  EXPECT_EQ(DpiRuntime::SvLow(h), 0u);
  EXPECT_EQ(DpiRuntime::SvHigh(h), 9u);
  EXPECT_EQ(DpiRuntime::SvSize(h), 10u);
}

TEST(DpiRuntime, OpenArrayEmptyHandle) {
  svOpenArrayHandle h;
  h.data = nullptr;
  h.size = 0;
  h.elem_width = 0;

  EXPECT_EQ(DpiRuntime::SvLow(h), 0u);
  EXPECT_EQ(DpiRuntime::SvHigh(h), 0u);
  EXPECT_EQ(DpiRuntime::SvSize(h), 0u);
}

// =============================================================================
// Pure vs context function semantics (S35.5.3)
// =============================================================================

TEST(DpiRuntime, PureFunctionFlag) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_pure";
  func.sv_name = "sv_pure";
  func.is_pure = true;
  func.is_context = false;
  func.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() + 1);
  };
  rt.RegisterImport(func);

  const auto* found = rt.FindImport("sv_pure");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_pure);
  EXPECT_FALSE(found->is_context);
}

TEST(DpiRuntime, ContextFunctionFlag) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_ctx";
  func.sv_name = "sv_ctx";
  func.is_pure = false;
  func.is_context = true;
  func.impl = [](const std::vector<DpiArgValue>& /*args*/) -> DpiArgValue {
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(func);

  const auto* found = rt.FindImport("sv_ctx");
  ASSERT_NE(found, nullptr);
  EXPECT_FALSE(found->is_pure);
  EXPECT_TRUE(found->is_context);
}

TEST(DpiRuntime, PopEmptyScopeDoesNotCrash) {
  DpiRuntime rt;
  rt.PopScope();  // Should not crash.
  EXPECT_EQ(rt.CurrentScope(), nullptr);
}
