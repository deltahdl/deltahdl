// Annex H.10.1.1: Scalars of type bit and logic

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiRuntime, ArgValueBit) {
  auto v = DpiArgValue::FromBit(1);
  EXPECT_EQ(v.type, DataTypeKind::kBit);
  EXPECT_EQ(v.AsBit(), 1);
}

}  // namespace
