// §35.6: Calling imported functions

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulation/dpi_runtime.h"

using namespace delta;

namespace {

// =============================================================================
// DpiRuntime: import registration and invocation
// =============================================================================
TEST(DpiRuntime, RegisterImportAndCall) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_add";
  func.sv_name = "sv_add";
  func.return_type = DataTypeKind::kInt;
  func.impl = [](const std::vector<DpiArgValue> &args) -> DpiArgValue {
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
  func.impl = [](const std::vector<DpiArgValue> &args) -> DpiArgValue {
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
  func.impl = [](const std::vector<DpiArgValue> &args) -> DpiArgValue {
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
  func.impl = [](const std::vector<DpiArgValue> &args) -> DpiArgValue {
    return DpiArgValue::FromChandle(args[0].AsChandle());
  };
  rt.RegisterImport(func);

  int dummy = 42;
  auto result =
      rt.CallImport("sv_identity", {DpiArgValue::FromChandle(&dummy)});
  EXPECT_EQ(result.AsChandle(), &dummy);
}

}  // namespace
