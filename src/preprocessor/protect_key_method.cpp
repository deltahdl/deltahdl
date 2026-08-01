#include "preprocessor/protect_key_method.h"

#include <span>
#include <string>
#include <string_view>

#include "preprocessor/protect_keywords.h"

namespace delta {
namespace {

// The table of encryption algorithm identifiers, in the order it lists them:
// the identifier, whether every implementation provides the cipher behind it,
// and the published cipher the identifier stands for.
//
// One identifier is marked required, so it is the one a tool may be handed a
// block under without having been told anything about the tool that wrote it.
// The rest are named here without being provided, which is what the optional
// column allows: what the table asks of an implementation offering one of them
// is that it offer it under this name rather than a name of its own.
//
// The list is the one §34.5.11 writes for the cipher a region's data are under.
// §34.5.24 gives the cipher a region's keys are under no list of its own and
// sends the reader to that one, so what is written once here answers for both
// keywords -- a second copy would be a second place for the two to drift apart
// in, and the standard gives them one set of values rather than two alike.
constexpr ProtectEncryptionAlgorithm kProtectEncryptionAlgorithms[] = {
    {"des-cbc", true, "Data Encryption Standard in CBC mode, see FIPS 46-3"},
    {"3des-cbc", false,
     "Triple DES in CBC mode, see FIPS 46-3 and ANSI X9.52-1998"},
    {"aes128-cbc", false,
     "Advanced Encryption Standard in CBC mode, 128-bit key, see FIPS 197"},
    {"aes256-cbc", false, "AES in CBC mode with a 256-bit key"},
    {"aes192-cbc", false, "AES in CBC mode with a 192-bit key"},
    {"blowfish-cbc", false, "Blowfish in CBC mode, see Schneier"},
    {"twofish256-cbc", false,
     "Twofish in CBC mode with a 256-bit key, see Schneier"},
    {"twofish192-cbc", false, "Twofish in CBC mode with a 192-bit key"},
    {"twofish128-cbc", false, "Twofish in CBC mode with a 128-bit key"},
    {"serpent256-cbc", false,
     "Serpent in CBC mode with a 256-bit key, see Anderson et al."},
    {"serpent192-cbc", false, "Serpent in CBC mode with a 192-bit key"},
    {"serpent128-cbc", false, "Serpent in CBC mode with a 128-bit key"},
    {"cast128-cbc", false, "CAST-128 in CBC mode, see IETF RFC 2144"},
    {"rsa", false, "RSA, see IETF RFC 2437"},
    {"elgamal", false, "ElGamal"},
    {"pgp-rsa", false, "OpenPGP RSA key, see IETF RFC 2440"},
};

const ProtectEncryptionAlgorithm* RowOfEncryptionTable(
    std::string_view identifier) {
  for (const ProtectEncryptionAlgorithm& row : kProtectEncryptionAlgorithms) {
    if (row.identifier == identifier) return &row;
  }
  return nullptr;
}

}  // namespace

std::span<const ProtectEncryptionAlgorithm> ProtectEncryptionAlgorithms() {
  return kProtectEncryptionAlgorithms;
}

// The values this keyword identifies a cipher by are the tabulated ones, that
// being the whole of what the subclause says about which values it takes: it
// admits the identifiers the other method keyword admits and adds none.
bool IsProtectKeyMethodIdentifier(std::string_view identifier) {
  return RowOfEncryptionTable(identifier) != nullptr;
}

bool IsRequiredProtectEncryptionAlgorithm(std::string_view identifier) {
  const ProtectEncryptionAlgorithm* row = RowOfEncryptionTable(identifier);
  return row != nullptr && row->required;
}

// A directive that wrote the keyword with nothing against it named no cipher
// any more than leaving the keyword out did, so nothing stands in effect in
// either case and both are reported the same way. What a reader does with that
// is decline to open a key block rather than open one under a guess: a block
// opened under the wrong cipher yields bytes, and bytes are what a block
// opened under the right one yields too.
ProtectKeywordValue ProtectKeyMethodInEffect(const ProtectKeywordScope& scope) {
  ProtectKeywordValue written = scope.ValueOf(kKeyMethodKeyword);
  if (!written.defaulted && !written.value.empty()) return written;
  return {std::string(), true};
}

}  // namespace delta
