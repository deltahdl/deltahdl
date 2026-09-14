#pragma once

#include <cstdint>
#include <span>
#include <string_view>

namespace delta {

// Annex O: the encryption/decryption flow. §O.1 has the annex describe a
// number of scenarios that can be used for IP protection, and show how the
// relevant pragmas -- the protect pragma's, whose keywords §34.4 tabulates --
// are used to achieve the desired effect of securely protecting, distributing
// and decrypting the model. The annex is informative: what it describes is
// how the pragmas of Clause 34 are put to use, and each scenario is a use of
// them rather than a rule of its own. This header states what §O.1 says; the
// scenarios themselves are §O.3 through §O.5, and the pragmas they use are
// processed where Clause 34 is.

// §O.1: the annex that describes the scenarios.
std::string_view AnnexDescribingProtectionScenarios();

// §O.1: the annex is informative, not normative.
bool ProtectionScenariosAreInformative();

// §O.1: the scenarios the annex describes, one per subclause from §O.3 on:
// the tool vendor secret key encryption system, the IP author secret key
// encryption system, and digital envelopes.
enum class ProtectionScenario : std::uint8_t {
  kToolVendorSecretKey,
  kIpAuthorSecretKey,
  kDigitalEnvelope,
};
std::span<const ProtectionScenario> ProtectionScenariosDescribed();

// §O.1: the pragma whose use the scenarios show, the protect pragma of §34.2.
std::string_view PragmaUsedForProtection();

// §O.1: the effects the pragmas are used to achieve -- securely protecting
// the model, distributing it, and decrypting it.
enum class ProtectionEffect : std::uint8_t {
  kSecurelyProtecting,
  kDistributing,
  kDecrypting,
};
std::span<const ProtectionEffect> EffectsThePragmasAchieve();

}  // namespace delta
