#include <gtest/gtest.h>

#include <string_view>

#include "simulator/vpi_include_file.h"

#define VPI_COMPATIBILITY_VERSION_1364v1995 1
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

#define ANNEX_L_01_STR(x) #x
#define ANNEX_L_01_XSTR(x) ANNEX_L_01_STR(x)

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

TEST(VpiCompatibilityHeaderProvided,
     VpiUserHIncludesTheFileAndApplicationCodeDoesNot) {
  EXPECT_TRUE(VpiCompatibilityHIsIncludedAutomatically());
  EXPECT_TRUE(
      VpiCompatibilityHIsIncludedBy(VpiCompatibilityHIncluder::kVpiUserH));
  EXPECT_FALSE(VpiCompatibilityHIsIncludedBy(
      VpiCompatibilityHIncluder::kUserApplicationCode));
}

TEST(VpiCompatibilityHeaderProvided, IncludingVpiUserHReadsTheFile) {
#ifdef VPI_COMPATIBILITY_H
  SUCCEED();
#else
  FAIL() << "vpi_user.h did not include vpi_compatibility.h";
#endif
}

TEST(VpiCompatibilityHeaderProvided,
     TheModeSelectedTakesEffectThroughVpiUserH) {
  EXPECT_STREQ(ANNEX_L_01_XSTR(vpi_get), "vpi_get_1364v1995");
  EXPECT_STREQ(ANNEX_L_01_XSTR(vpi_get_value), "vpi_get_value_1364v1995");
  EXPECT_STREQ(ANNEX_L_01_XSTR(vpi_register_cb), "vpi_register_cb_1364v1995");
  EXPECT_STREQ(ANNEX_L_01_XSTR(vpi_printf), "vpi_printf");
}

}  // namespace
