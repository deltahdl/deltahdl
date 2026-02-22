// Annex H.7: Data types

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <vector>
#include "simulation/dpi_runtime.h"

using namespace delta;

namespace {

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

}  // namespace
