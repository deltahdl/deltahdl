#pragma once

#include <cstdint>
#include <span>
#include <string_view>

namespace delta {

std::string_view AnnexDescribingProtectionScenarios();

bool ProtectionScenariosAreInformative();

enum class ProtectionScenario : std::uint8_t {
  kToolVendorSecretKey,
  kIpAuthorSecretKey,
  kDigitalEnvelope,
};
std::span<const ProtectionScenario> ProtectionScenariosDescribed();

std::string_view PragmaUsedForProtection();

enum class ProtectionEffect : std::uint8_t {
  kSecurelyProtecting,
  kDistributing,
  kDecrypting,
};
std::span<const ProtectionEffect> EffectsThePragmasAchieve();

std::string_view KeywordOpeningTheProtectedBlock();
std::string_view KeywordClosingTheProtectedBlock();

enum class ProtectionThreat : std::uint8_t {
  kInappropriateAccess,
  kUnauthorizedModification,
};
std::span<const ProtectionThreat> ThreatsTheBlockProtectsFrom();

bool InformationInTheBlockIsProtectedOnceEncrypted();

bool ToolVendorSecretKeyIsEmbeddedInTheTool();
bool ToolVendorSecretKeyEncryptsAndDecrypts();
bool ToolVendorSecretKeySystemIsToolVendorSpecific();
std::string_view DirectiveTheToolVendorSecretKeySystemIsEquivalentTo();

bool ToolEmbedsAVendorSecretKey();

std::span<const std::string_view> PragmasRequiredByToolVendorSecretKeyInput();
std::span<const std::string_view> PragmasOptionalInToolVendorSecretKeyInput();

bool CleartextIsCopiedToTheToolVendorSecretKeyOutput();
std::span<const std::string_view>
ExpressionsTheToolVendorSecretKeyOutputCarries();
std::span<const std::string_view>
WhatTheToolVendorSecretKeyDataBlockIsComposedOf();

bool IpAuthorSecretKeyEncryptsWithTheAuthorsPublicKey();
bool IpAuthorSecretKeyDecryptsWithThePrivateKeyInTheToolsDatabase();
bool IpAuthorsProvideTheirPrivateKeysToTheToolsDatabase();

bool ToolsKeyDatabaseIsTheKeysGivenToTheRun();
bool ToolDerivesADecryptionKeyFromTheAuthorsEncryptionKey();

std::span<const std::string_view> PragmasRequiredByIpAuthorSecretKeyInput();
std::span<const std::string_view> PragmasOptionalInIpAuthorSecretKeyInput();
bool IpAuthorSecretKeyDataMethodNamesAPublicPrivateScheme();

bool ToolProvidesAPublicPrivateEncryptionScheme();

bool CleartextIsCopiedToTheIpAuthorSecretKeyOutput();
std::span<const std::string_view>
ExpressionsTheIpAuthorSecretKeyOutputCarries();
std::span<const std::string_view>
WhatTheIpAuthorSecretKeyDataBlockIsComposedOf();
bool IpAuthorSecretKeyOutputNamesThePublicPrivateSchemeAsItsMethod();

bool DigitalEnvelopeEncryptsTheDesignUnderASymmetricKey();
bool DigitalEnvelopeEncryptsTheSymmetricKeyUnderTheRecipientsPublicKey();
std::string_view KeywordRecordingTheEncryptedSymmetricKey();
bool DigitalEnvelopesCanBeCreatedUnderEitherSecretKeyScheme();
bool AnEnvelopeWithSeveralKeyBlocksOpensToSeveralRecipients();

enum class DataKeySpecification : std::uint8_t {
  kKeyownerAndKeyname,
  kDataDecryptKey,
};
DataKeySpecification DataKeySpecificationNeedingTheKeyAtTheDecryptingTool();
DataKeySpecification DataKeySpecificationTheAnnexPrefers();
DataKeySpecification DataKeySpecificationThisToolWritesIntoAKeyBlock();

std::span<const std::string_view> PragmasExpectedByDigitalEnvelopeInput();
std::span<const std::string_view> PragmasOptionalInDigitalEnvelopeInput();
bool DataKeyownerShallBeTheOwnerOfTheKeyNameProvided();

std::span<const std::string_view> KeyMethodsThisToolSealsAKeyBlockUnder();

bool CleartextIsCopiedToTheDigitalEnvelopeOutput();
std::span<const std::string_view> ExpressionsTheDigitalEnvelopeOutputCarries();
std::span<const std::string_view> WhatTheDigitalEnvelopeKeyBlockContains();
std::span<const std::string_view> WhatTheDigitalEnvelopeDataBlockIsComposedOf();
bool DigitalEnvelopeKeyBlockDataStandBeneathTheKeyword();

}  // namespace delta
