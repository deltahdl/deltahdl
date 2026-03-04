// Non-LRM tests

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <vector>
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

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

}  // namespace
