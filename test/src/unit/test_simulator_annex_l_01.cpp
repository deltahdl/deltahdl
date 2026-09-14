#include <gtest/gtest.h>

#include <string_view>

#include "simulator/vpi_include_file.h"

// §L.1 says of vpi_compatibility.h that vpi_user.h includes it automatically
// and that user application code therefore does not include it directly. This
// file is written as such application code: it selects a compatibility mode
// and includes vpi_user.h alone, never naming the file Annex L shows, and
// observes that the file was read all the same -- its guard is defined and
// the mode selected took effect through it.
#define VPI_COMPATIBILITY_VERSION_1364v1995 1
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

// Expand-then-stringize, so the spelling a routine name has after the
// preprocessor can be compared as text.
#define ANNEX_L_01_STR(x) #x
#define ANNEX_L_01_XSTR(x) ANNEX_L_01_STR(x)

// §L.1: Annex L shows the contents of vpi_compatibility.h, the file holding
// the special macro definitions required to support VPI compatibility mode
// functionality, which §36.12 describes and §36.12.2.1 especially.
TEST(VpiCompatibilityHeaderProvided,
     TheAnnexShowsTheFileSupportingCompatibilityMode) {
  EXPECT_EQ(VpiAnnexShowingVpiCompatibilityH(), "Annex L");
  EXPECT_EQ(VpiCompatibilityHFileName(), "vpi_compatibility.h");
  EXPECT_EQ(VpiCompatibilityHSupports(),
            VpiIncludeFileSupport::kVpiCompatibilityMode);
  auto subclauses = VpiCompatibilityHSubclausesDescribingItsSupport();
  EXPECT_EQ(subclauses[0], "36.12");
  EXPECT_EQ(subclauses[1], "36.12.2.1");
}

// §L.1: vpi_user.h includes the file automatically, and user application
// code therefore does not include it directly.
TEST(VpiCompatibilityHeaderProvided,
     VpiUserHIncludesTheFileAndApplicationCodeDoesNot) {
  EXPECT_TRUE(VpiCompatibilityHIsIncludedAutomatically());
  EXPECT_TRUE(
      VpiCompatibilityHIsIncludedBy(VpiCompatibilityHIncluder::kVpiUserH));
  EXPECT_FALSE(VpiCompatibilityHIsIncludedBy(
      VpiCompatibilityHIncluder::kUserApplicationCode));
}

// §L.1: the inclusion is automatic -- this file named vpi_user.h only, and
// the mark src/simulator/vpi_compatibility.h leaves of its reading is defined
// once that include has been read.
TEST(VpiCompatibilityHeaderProvided, IncludingVpiUserHReadsTheFile) {
#ifdef VPI_COMPATIBILITY_H
  SUCCEED();
#else
  FAIL() << "vpi_user.h did not include vpi_compatibility.h";
#endif
}

// §L.1: the file's macro definitions are what support the compatibility
// mode, and they reach application code through vpi_user.h alone: the
// 1364v1995 mode this file selected before its one include retargets the
// standard routine names to that mode's variants, and a routine §36.12.2.1
// does not list keeps its name.
TEST(VpiCompatibilityHeaderProvided,
     TheModeSelectedTakesEffectThroughVpiUserH) {
  EXPECT_STREQ(ANNEX_L_01_XSTR(vpi_get), "vpi_get_1364v1995");
  EXPECT_STREQ(ANNEX_L_01_XSTR(vpi_get_value), "vpi_get_value_1364v1995");
  EXPECT_STREQ(ANNEX_L_01_XSTR(vpi_register_cb), "vpi_register_cb_1364v1995");
  EXPECT_STREQ(ANNEX_L_01_XSTR(vpi_printf), "vpi_printf");
}

}  // namespace
