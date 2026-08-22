#include <gtest/gtest.h>

#include <type_traits>

#include "simulator/svdpi.h"

namespace {

// H.10.1.3 declares svScope as `typedef void *svScope;` -- "a handle to a scope
// (an instance of a module or an interface)". A foreign object file is compiled
// against its own copy of svdpi.h, so every entry point taking a scope is
// linked by a signature this spelling decides. A handle declared const, or
// narrowed to a pointer to a named struct, would compile here and change that
// signature.
TEST(SvDpi, ScopeHandleIsTheVoidPointerTheClauseDeclares) {
  EXPECT_TRUE((std::is_same_v<svScope, void*>));
}

// H.10.1.3 declares svOpenArrayHandle as `typedef void* svOpenArrayHandle;` --
// "a handle to a generic object (actually, unsized array)". It is asserted
// apart from svScope because the clause declares the two separately and a
// change to either alone would leave the other's assertion green.
TEST(SvDpi, OpenArrayHandleIsTheVoidPointerTheClauseDeclares) {
  EXPECT_TRUE((std::is_same_v<svOpenArrayHandle, void*>));
}

// H.10.1.3: a tool using the VPI-based canonical value representation reports
// the version string "1800-2005". This simulator uses s_vpi_vecval as its
// canonical value, so svDpiVersion() shall return exactly that string.
TEST(SvDpi, DpiVersionReportsVpiCanonicalRepresentation) {
  const char* ver = svDpiVersion();
  ASSERT_NE(ver, nullptr);
  EXPECT_STREQ(ver, "1800-2005");
}

// H.10.1.3 has svDpiVersion() report "which DPI standard is supported by the
// simulator and in particular which canonical value representation is being
// provided", and it pairs each of the two permitted strings with one
// representation: "1800-2005" with the VPI-based canonical value, "SV3.1a" with
// Accellera's svLogicVec32. The string and the type are therefore one answer
// given twice, and a change to the representation that left the string alone
// would tell a foreign caller to read the wrong layout. This reads the type
// back after the string, so neither can move without the other.
TEST(SvDpi, DpiVersionNamesTheCanonicalValueThatSvdpiProvides) {
  ASSERT_STREQ(svDpiVersion(), "1800-2005");
  EXPECT_TRUE((std::is_same_v<svLogicVecVal, s_vpi_vecval>));
}

}  // namespace
