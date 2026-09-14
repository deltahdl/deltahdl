#include <gtest/gtest.h>

#include <algorithm>

#include "preprocessor/protect_flow.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

namespace {

// §O.1: Annex O, an informative annex, describes a number of scenarios that
// can be used for IP protection -- three of them, one per subclause from
// §O.3: a tool vendor's secret key, an IP author's secret key, and digital
// envelopes.
TEST(EncryptionFlowGeneral, TheAnnexDescribesThreeScenariosInformatively) {
  EXPECT_EQ(AnnexDescribingProtectionScenarios(), "Annex O");
  EXPECT_TRUE(ProtectionScenariosAreInformative());
  auto scenarios = ProtectionScenariosDescribed();
  ASSERT_EQ(scenarios.size(), 3u);
  EXPECT_EQ(scenarios[0], ProtectionScenario::kToolVendorSecretKey);
  EXPECT_EQ(scenarios[1], ProtectionScenario::kIpAuthorSecretKey);
  EXPECT_EQ(scenarios[2], ProtectionScenario::kDigitalEnvelope);
}

// §O.1: the annex shows how the relevant pragmas are used to achieve the
// desired effect of securely protecting, distributing and decrypting the
// model. The pragma is the protect pragma of §34.2, and the three effects are
// the ones the annex names.
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

// §O.1 with §O.2: the pragmas the annex's scenarios use are the protect
// pragma's keywords, and the region they protect is a begin-end block; both
// keywords the annex's overview names are ones §34.4 tabulates, so a source
// writing them writes the pragma the annex describes and not a pragma of some
// other name.
TEST(EncryptionFlowGeneral, TheRelevantPragmasAreTheProtectPragmasKeywords) {
  EXPECT_TRUE(IsProtectPragmaKeyword("begin"));
  EXPECT_TRUE(IsProtectPragmaKeyword("end"));
  EXPECT_TRUE(IsProtectPragmaKeyword("data_keyname"));
  EXPECT_FALSE(IsProtectPragmaKeyword("scenario"));
}

}  // namespace
