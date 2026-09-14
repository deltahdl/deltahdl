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

// §O.2: the data to be protected is placed within a protect begin-end block,
// the block the protect pragma's begin and end keywords delimit.
std::string_view KeywordOpeningTheProtectedBlock();
std::string_view KeywordClosingTheProtectedBlock();

// §O.2: what the block protects the data from -- inappropriate access, and
// unauthorized modification.
enum class ProtectionThreat : std::uint8_t {
  kInappropriateAccess,
  kUnauthorizedModification,
};
std::span<const ProtectionThreat> ThreatsTheBlockProtectsFrom();

// §O.2: information written in the block, once encrypted, is protected as
// the data is -- a pragma expression the author writes inside the block is
// encrypted with the block rather than standing in the clear outside it.
bool InformationInTheBlockIsProtectedOnceEncrypted();

// §O.3: in the tool vendor secret key encryption system the key is the tool
// vendor's own, proprietary and embedded within the tool itself, and the same
// key serves both encryption and decryption -- the simplest scenario in the
// EDA domain, roughly equivalent to the historical `protect technique, whose
// drawback is that it is completely tool-vendor-specific: the IP author
// encrypts the IP, and any IP consumer with appropriate licences and the same
// tool vendor can use it.
bool ToolVendorSecretKeyIsEmbeddedInTheTool();
bool ToolVendorSecretKeyEncryptsAndDecrypts();
bool ToolVendorSecretKeySystemIsToolVendorSpecific();
std::string_view DirectiveTheToolVendorSecretKeySystemIsEquivalentTo();

// §O.3 as this tool has it: the scenario turns on a key the vendor keeps
// secret inside the tool, and this tool embeds none. Every key it holds is
// one it was given under §34.5.10's owner and name, or the exchange key of
// §34.3.1, on the command line of the run -- so the same key given to the
// encrypting run and to the decrypting run is what stands in for the
// vendor's, and a decrypting run given no key opens nothing.
bool ToolEmbedsAVendorSecretKey();

// §O.3.1: the pragmas the encryption input of the tool vendor secret key
// system requires -- data_keyname naming one of the tool's embedded keys, and
// begin and end surrounding the regions to be encrypted -- and the further
// ones the input may include: the author's name and information, the key
// owner of the name provided, a method appropriate for the key where the
// default rounds, initialization vector or key width are not what is wanted,
// a different encoding, a digest block where a message authorization code is
// wanted, and a decryption or a run-time licence where the author wants one.
// Each is a keyword §34.4 tabulates for the protect pragma.
std::span<const std::string_view> PragmasRequiredByToolVendorSecretKeyInput();
std::span<const std::string_view> PragmasOptionalInToolVendorSecretKeyInput();

// §O.3.2: the encrypting tool should take the input file and copy all
// cleartext to the corresponding output sections, and for each protect
// begin-end block generate begin_protected to start the protected region,
// then data_keyowner, data_keyname, data_method and encoding, author and
// author_info if the input provided them, digest_block followed by the
// encoded encrypted digest, data_block followed by the encoded encrypted data
// composed of the licences and the text found between begin and end, and
// end_protected. The annex writes the second licence as encrypt_license, a
// name §34.4 does not tabulate and §O.3.1's input does not list; the licence
// that input lists beside decrypt_license is runtime_license, and that is
// what the data are read as composed of here.
bool CleartextIsCopiedToTheToolVendorSecretKeyOutput();
std::span<const std::string_view>
ExpressionsTheToolVendorSecretKeyOutputCarries();
std::span<const std::string_view>
WhatTheToolVendorSecretKeyDataBlockIsComposedOf();

}  // namespace delta
