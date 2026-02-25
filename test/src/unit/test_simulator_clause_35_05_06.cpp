// §35.5.6: Types of formal arguments

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulation/dpi_runtime.h"

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

}  // namespace
