// Annex H.8.10: String arguments

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <vector>
#include "simulation/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiRuntime, ArgValueString) {
  auto v = DpiArgValue::FromString("hello");
  EXPECT_EQ(v.type, DataTypeKind::kString);
  EXPECT_EQ(v.AsString(), "hello");
}

}  // namespace
