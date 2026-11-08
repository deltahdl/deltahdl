#include <gtest/gtest.h>

#include <type_traits>

#include "simulator/svdpi.h"

namespace {

TEST(SvDpi, ScopeHandleIsTheVoidPointerTheClauseDeclares) {
  EXPECT_TRUE((std::is_same_v<svScope, void*>));
}

TEST(SvDpi, OpenArrayHandleIsTheVoidPointerTheClauseDeclares) {
  EXPECT_TRUE((std::is_same_v<svOpenArrayHandle, void*>));
}

TEST(SvDpi, DpiVersionReportsVpiCanonicalRepresentation) {
  const char* ver = svDpiVersion();
  ASSERT_NE(ver, nullptr);
  EXPECT_STREQ(ver, "1800-2005");
}

TEST(SvDpi, DpiVersionNamesTheCanonicalValueThatSvdpiProvides) {
  ASSERT_STREQ(svDpiVersion(), "1800-2005");
  EXPECT_TRUE((std::is_same_v<svLogicVecVal, s_vpi_vecval>));
}

}  // namespace
