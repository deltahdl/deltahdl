#include <gtest/gtest.h>

#include <array>

#include "simulator/foreign_code.h"

using namespace delta;

namespace {

TEST(ForeignCodeOverview, TheAnnexAppliesToDpiIncludedCodeOfAnyLanguage) {
  EXPECT_TRUE(ForeignCodeAnnexApplies(ForeignCodeInterface::kDpi));
  EXPECT_FALSE(ForeignCodeAnnexApplies(ForeignCodeInterface::kVpi));
  EXPECT_FALSE(ForeignCodeIsLimitedToCOrCpp());
}

TEST(ForeignCodeOverview, ObjectCodeIsTheFormEverySimulatorSupports) {
  EXPECT_EQ(ForeignCodeProvidedForm(), ForeignCodeForm::kObjectCode);
  EXPECT_TRUE(ForeignCodeObjectFormMustBeSupported());
}

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
