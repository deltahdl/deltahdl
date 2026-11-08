#include <gtest/gtest.h>

#include <algorithm>

#include "preprocessor/protect_flow.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

namespace {

TEST(EncryptionFlowGeneral, TheAnnexDescribesThreeScenariosInformatively) {
  EXPECT_EQ(AnnexDescribingProtectionScenarios(), "Annex O");
  EXPECT_TRUE(ProtectionScenariosAreInformative());
  auto scenarios = ProtectionScenariosDescribed();
  ASSERT_EQ(scenarios.size(), 3u);
  EXPECT_EQ(scenarios[0], ProtectionScenario::kToolVendorSecretKey);
  EXPECT_EQ(scenarios[1], ProtectionScenario::kIpAuthorSecretKey);
  EXPECT_EQ(scenarios[2], ProtectionScenario::kDigitalEnvelope);
}

TEST(EncryptionFlowGeneral,
     ThePragmasAchieveProtectionDistributionAndDecryption) {
  EXPECT_EQ(PragmaUsedForProtection(), "protect");
  auto effects = EffectsThePragmasAchieve();
  ASSERT_EQ(effects.size(), 3u);
  EXPECT_NE(std::find(effects.begin(), effects.end(),
                      ProtectionEffect::kSecurelyProtecting),
            effects.end());
  EXPECT_NE(std::find(effects.begin(), effects.end(),
                      ProtectionEffect::kDistributing),
            effects.end());
  EXPECT_NE(
      std::find(effects.begin(), effects.end(), ProtectionEffect::kDecrypting),
      effects.end());
}

TEST(EncryptionFlowGeneral, TheRelevantPragmasAreTheProtectPragmasKeywords) {
  EXPECT_TRUE(IsProtectPragmaKeyword("begin"));
  EXPECT_TRUE(IsProtectPragmaKeyword("end"));
  EXPECT_TRUE(IsProtectPragmaKeyword("data_keyname"));
  EXPECT_FALSE(IsProtectPragmaKeyword("scenario"));
}

}  // namespace
