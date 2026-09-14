#include "preprocessor/protect_flow.h"

#include <span>
#include <string_view>

#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_license.h"
#include "preprocessor/protect_processing.h"

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

std::string_view KeywordOpeningTheProtectedBlock() {
  return kBeginEncryptionKeyword;
}

std::string_view KeywordClosingTheProtectedBlock() {
  return kEndEncryptionKeyword;
}

std::span<const ProtectionThreat> ThreatsTheBlockProtectsFrom() {
  static constexpr ProtectionThreat kThreats[] = {
      ProtectionThreat::kInappropriateAccess,
      ProtectionThreat::kUnauthorizedModification,
  };
  return kThreats;
}

bool InformationInTheBlockIsProtectedOnceEncrypted() { return true; }

bool ToolVendorSecretKeyIsEmbeddedInTheTool() { return true; }

bool ToolVendorSecretKeyEncryptsAndDecrypts() { return true; }

bool ToolVendorSecretKeySystemIsToolVendorSpecific() { return true; }

std::string_view DirectiveTheToolVendorSecretKeySystemIsEquivalentTo() {
  return "`protect";
}

bool ToolEmbedsAVendorSecretKey() { return false; }

std::span<const std::string_view> PragmasRequiredByToolVendorSecretKeyInput() {
  static constexpr std::string_view kRequired[] = {
      kDataKeynameKeyword,
      kBeginEncryptionKeyword,
      kEndEncryptionKeyword,
  };
  return kRequired;
}

std::span<const std::string_view> PragmasOptionalInToolVendorSecretKeyInput() {
  static constexpr std::string_view kOptional[] = {
      kAuthorKeyword,         kAuthorInfoKeyword,     kDataKeyownerKeyword,
      kDataMethodKeyword,     kEncodingKeyword,       kDigestBlockKeyword,
      kDecryptLicenseKeyword, kRuntimeLicenseKeyword,
  };
  return kOptional;
}

bool CleartextIsCopiedToTheToolVendorSecretKeyOutput() { return true; }

std::span<const std::string_view>
ExpressionsTheToolVendorSecretKeyOutputCarries() {
  static constexpr std::string_view kExpressions[] = {
      kBeginDecryptionKeyword, kDataKeyownerKeyword, kDataKeynameKeyword,
      kDataMethodKeyword,      kEncodingKeyword,     kAuthorKeyword,
      kAuthorInfoKeyword,      kDigestBlockKeyword,  kDataBlockKeyword,
      kEndDecryptionKeyword,
  };
  return kExpressions;
}

std::span<const std::string_view>
WhatTheToolVendorSecretKeyDataBlockIsComposedOf() {
  static constexpr std::string_view kComposition[] = {
      kDecryptLicenseKeyword,
      kRuntimeLicenseKeyword,
      "the text found between begin and end",
  };
  return kComposition;
}

bool IpAuthorSecretKeyEncryptsWithTheAuthorsPublicKey() { return true; }

bool IpAuthorSecretKeyDecryptsWithThePrivateKeyInTheToolsDatabase() {
  return true;
}

bool IpAuthorsProvideTheirPrivateKeysToTheToolsDatabase() { return true; }

bool ToolsKeyDatabaseIsTheKeysGivenToTheRun() { return true; }

bool ToolDerivesADecryptionKeyFromTheAuthorsEncryptionKey() { return false; }

std::span<const std::string_view> PragmasRequiredByIpAuthorSecretKeyInput() {
  return PragmasRequiredByToolVendorSecretKeyInput();
}

std::span<const std::string_view> PragmasOptionalInIpAuthorSecretKeyInput() {
  return PragmasOptionalInToolVendorSecretKeyInput();
}

bool IpAuthorSecretKeyDataMethodNamesAPublicPrivateScheme() { return true; }

bool ToolProvidesAPublicPrivateEncryptionScheme() { return false; }

}  // namespace delta
