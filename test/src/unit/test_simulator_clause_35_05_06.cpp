#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiRuntime, ArgValueLongint) {
  auto v = DpiArgValue::FromLongint(0x1'0000'0000LL);
  EXPECT_EQ(v.type, DataTypeKind::kLongint);
  EXPECT_EQ(v.AsLongint(), 0x1'0000'0000LL);
}

TEST(DpiRuntime, ArgValueChandle) {
  int dummy = 0;
  auto v = DpiArgValue::FromChandle(&dummy);
  EXPECT_EQ(v.type, DataTypeKind::kChandle);
  EXPECT_EQ(v.AsChandle(), &dummy);
}

TEST(DpiRuntime, ArgValueLogic) {
  auto v = DpiArgValue::FromLogic(0);
  EXPECT_EQ(v.type, DataTypeKind::kLogic);
  EXPECT_EQ(v.AsLogic(), 0);
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

}
