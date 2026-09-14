#include "preprocessor/protect_flow.h"

#include <span>
#include <string_view>

#include "preprocessor/protect_envelope.h"

namespace delta {

std::string_view AnnexDescribingProtectionScenarios() { return "Annex O"; }

bool ProtectionScenariosAreInformative() { return true; }

std::span<const ProtectionScenario> ProtectionScenariosDescribed() {
  static constexpr ProtectionScenario kScenarios[] = {
      ProtectionScenario::kToolVendorSecretKey,
      ProtectionScenario::kIpAuthorSecretKey,
      ProtectionScenario::kDigitalEnvelope,
  };
  return kScenarios;
}

std::string_view PragmaUsedForProtection() { return kProtectPragmaName; }

std::span<const ProtectionEffect> EffectsThePragmasAchieve() {
  static constexpr ProtectionEffect kEffects[] = {
      ProtectionEffect::kSecurelyProtecting,
      ProtectionEffect::kDistributing,
      ProtectionEffect::kDecrypting,
  };
  return kEffects;
}

}  // namespace delta
