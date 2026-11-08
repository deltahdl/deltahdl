#include "preprocessor/protect_key_method.h"

#include <span>
#include <string>
#include <string_view>

#include "preprocessor/protect_keywords.h"

namespace delta {
namespace {

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

bool IsProtectKeyMethodIdentifier(std::string_view identifier) {
  return RowOfEncryptionTable(identifier) != nullptr;
}

bool IsRequiredProtectEncryptionAlgorithm(std::string_view identifier) {
  const ProtectEncryptionAlgorithm* row = RowOfEncryptionTable(identifier);
  return row != nullptr && row->required;
}

ProtectKeywordValue ProtectKeyMethodInEffect(const ProtectKeywordScope& scope) {
  ProtectKeywordValue written = scope.ValueOf(kKeyMethodKeyword);
  if (!written.defaulted && !written.value.empty()) return written;
  return {std::string(), true};
}

}  // namespace delta
