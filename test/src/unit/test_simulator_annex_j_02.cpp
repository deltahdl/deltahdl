#include <gtest/gtest.h>

#include <array>

#include "simulator/foreign_code.h"

using namespace delta;

namespace {

// §J.2: foreign language code is functionality included through the DPI,
// and the annex applies to that alone -- code included through the VPI is
// outside the standard's scope -- whatever language the object code came
// from.
TEST(ForeignCodeOverview, TheAnnexAppliesToDpiIncludedCodeOfAnyLanguage) {
  EXPECT_TRUE(ForeignCodeAnnexApplies(ForeignCodeInterface::kDpi));
  EXPECT_FALSE(ForeignCodeAnnexApplies(ForeignCodeInterface::kVpi));
  EXPECT_FALSE(ForeignCodeIsLimitedToCOrCpp());
}

// §J.2: the code is provided as object code compiled for the platform, a
// form every simulator shall support including.
TEST(ForeignCodeOverview, ObjectCodeIsTheFormEverySimulatorSupports) {
  EXPECT_EQ(ForeignCodeProvidedForm(), ForeignCodeForm::kObjectCode);
  EXPECT_TRUE(ForeignCodeObjectFormMustBeSupported());
}

// §J.2: the annex defines how to specify the location of the files, the
// files to be loaded, and the provision of the object code as a shared
// library or an archive.
TEST(ForeignCodeOverview, ThreeFacilitiesAreDefinedAndTwoPackagingsAllowed) {
  const std::array<ForeignCodeFacility, 3> kFacilities =
      ForeignCodeFacilitiesDefined();
  EXPECT_EQ(kFacilities[0], ForeignCodeFacility::kSpecifyLocationOfFiles);
  EXPECT_EQ(kFacilities[1], ForeignCodeFacility::kSpecifyFilesToLoad);
  EXPECT_EQ(kFacilities[2], ForeignCodeFacility::kProvideObjectCode);
  EXPECT_TRUE(ForeignCodeObjectMayBePackagedAs(
      ForeignCodeObjectPackaging::kSharedLibrary));
  EXPECT_TRUE(
      ForeignCodeObjectMayBePackagedAs(ForeignCodeObjectPackaging::kArchive));
}

// §J.2: usually two implementations of the facilities are required, for the
// different viewpoints -- a vendor's IP often covered by a bootstrap file, a
// project team's common set and a user's selections by tool switches, each
// able to use the bootstrap file too -- and the switch names the annex
// defines are recommendations rather than requirements.
TEST(ForeignCodeOverview, TwoMethodsServeThreeViewpoints) {
  EXPECT_EQ(ForeignCodeImplementationsUsuallyRequired(), 2u);
  EXPECT_EQ(ForeignCodeMethodOftenCovering(ForeignCodeUseCase::kVendorIp),
            ForeignCodeInclusionMethod::kBootstrapFile);
  EXPECT_EQ(ForeignCodeMethodOftenCovering(ForeignCodeUseCase::kProjectTeam),
            ForeignCodeInclusionMethod::kToolSwitches);
  EXPECT_EQ(ForeignCodeMethodOftenCovering(ForeignCodeUseCase::kUser),
            ForeignCodeInclusionMethod::kToolSwitches);
  EXPECT_TRUE(
      ForeignCodeUseCaseMayUseBootstrapFile(ForeignCodeUseCase::kVendorIp));
  EXPECT_TRUE(
      ForeignCodeUseCaseMayUseBootstrapFile(ForeignCodeUseCase::kProjectTeam));
  EXPECT_TRUE(ForeignCodeUseCaseMayUseBootstrapFile(ForeignCodeUseCase::kUser));
  EXPECT_FALSE(ForeignCodeSwitchNamesAreRequirements());
}

}  // namespace
