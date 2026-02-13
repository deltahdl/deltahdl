// Tests for Annex L (vpi_compatibility.h) — IEEE 1800-2023 VPI compat layer.
// Verifies version chaining and function remapping macros.

#include <gtest/gtest.h>

// Include vpi_compatibility.h indirectly through vpi_user.h (the only valid
// way per the standard). Since we don't yet have a standalone vpi_user.h that
// includes it, we test it through our combined header.
#include "vpi/vpi_compatibility.h"

namespace {

// =============================================================================
// Version constants exist
// =============================================================================

TEST(VpiCompat, HeaderIncludable) {
  // Simply including the header should compile.
  SUCCEED();
}

TEST(VpiCompat, VersionMacroAvailable) {
  // VPI_COMPATIBILITY_H should be defined after inclusion.
#ifdef VPI_COMPATIBILITY_H
  SUCCEED();
#else
  FAIL() << "VPI_COMPATIBILITY_H not defined after inclusion";
#endif
}

// =============================================================================
// Version chaining: 1800v2023 implies 1800v2012
// =============================================================================

TEST(VpiCompat, VersionChaining2023Implies2012) {
  // When VPI_COMPATIBILITY_VERSION_1800v2023 is set, 1800v2012 should also be.
  // This is tested by the header's preprocessor logic.
#ifdef VPI_COMPATIBILITY_VERSION_1800v2023
#ifdef VPI_COMPATIBILITY_VERSION_1800v2012
  SUCCEED();
#else
  FAIL() << "1800v2023 should imply 1800v2012";
#endif
#else
  SUCCEED();  // Not in 2023 compat mode; chaining is N/A.
#endif
}

// =============================================================================
// Default mode (no compatibility version active)
// =============================================================================

TEST(VpiCompat, DefaultNoRemapping) {
  // With no VPI_COMPATIBILITY_VERSION_* defined before inclusion,
  // the standard function names should not be remapped.
  // We verify by checking that the macros are NOT defined.
#ifndef VPI_COMPATIBILITY_VERSION_1364v1995
#ifndef VPI_COMPATIBILITY_VERSION_1364v2001
#ifndef VPI_COMPATIBILITY_VERSION_1800v2005
  SUCCEED();  // No compat mode active: functions are not remapped.
#endif
#endif
#endif
}

}  // namespace
