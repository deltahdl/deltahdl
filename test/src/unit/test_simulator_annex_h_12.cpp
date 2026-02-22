// Annex H.12: Open arrays

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulation/dpi_runtime.h"

using namespace delta;

namespace {

// =============================================================================
// DpiRuntime: open array support (S35.5.6)
// =============================================================================
TEST(DpiRuntime, OpenArrayHandleOperations) {
  SvOpenArrayHandle h;
  h.data = nullptr;
  h.size = 10;
  h.elem_width = 32;

  EXPECT_EQ(DpiRuntime::SvLow(h), 0u);
  EXPECT_EQ(DpiRuntime::SvHigh(h), 9u);
  EXPECT_EQ(DpiRuntime::SvSize(h), 10u);
}

TEST(DpiRuntime, OpenArrayEmptyHandle) {
  SvOpenArrayHandle h;
  h.data = nullptr;
  h.size = 0;
  h.elem_width = 0;

  EXPECT_EQ(DpiRuntime::SvLow(h), 0u);
  EXPECT_EQ(DpiRuntime::SvHigh(h), 0u);
  EXPECT_EQ(DpiRuntime::SvSize(h), 0u);
}

}  // namespace
