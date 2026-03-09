#include <gtest/gtest.h>

#include "simulator/svdpi.h"

namespace {

TEST(SvDpi, HandleTypes) {
  svScope scope = nullptr;
  svOpenArrayHandle arr = nullptr;
  EXPECT_EQ(scope, nullptr);
  EXPECT_EQ(arr, nullptr);
}

TEST(SvDpi, DpiVersionReturnsNonNull) {
  const char* ver = svDpiVersion();
  ASSERT_NE(ver, nullptr);
  EXPECT_GT(strlen(ver), 0u);
}

}  // namespace
