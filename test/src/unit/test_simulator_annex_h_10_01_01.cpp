// Annex H.10.1.1: Scalars of type bit and logic

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <vector>
#include "simulation/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiRuntime, ArgValueBit) {
  auto v = DpiArgValue::FromBit(1);
  EXPECT_EQ(v.type, DataTypeKind::kBit);
  EXPECT_EQ(v.AsBit(), 1);
}

// =============================================================================
// Canonical 4-value constants (Annex I)
// =============================================================================
TEST(SvDpi, CanonicalValueConstants) {
  EXPECT_EQ(sv_0, 0);
  EXPECT_EQ(sv_1, 1);
  EXPECT_EQ(sv_z, 2);
  EXPECT_EQ(sv_x, 3);
}

}  // namespace
