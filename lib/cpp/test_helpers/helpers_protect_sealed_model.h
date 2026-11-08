#pragma once

#include <cstddef>
#include <string>
#include <string_view>

#include "helpers_protect_keys.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

inline constexpr std::string_view kAuthorEntity = "Acme Corp";
inline constexpr std::string_view kAuthorKeyName = "design-2026";
inline constexpr std::string_view kAuthorKey = "acme-design-key";

inline constexpr std::string_view kAuthorPublicKey = "acme-public-key";

inline constexpr std::string_view kSealerEntity = "Other Corp";
inline constexpr std::string_view kSealerKeyName = "other-2019";
inline constexpr std::string_view kSealerKey = "other-legacy-key";

inline constexpr std::string_view kOuterStatement = "initial result = 42;";
inline constexpr std::string_view kInnerStatement = "initial sealed = 7;";

inline constexpr std::string_view kSealedBlockMarker = "SEALEDMODELBLOCKMARKER";

inline constexpr std::string_view kSealerMethod = "x-legacy-cipher";

inline constexpr std::string_view kCurrentMethod = "x-deltahdl-stream";

inline ProtectKeyList BothEntitiesKeys() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kAuthorEntity, kAuthorKeyName, kAuthorKey));
  keys.Add(KeyOf(kSealerEntity, kSealerKeyName, kSealerKey));
  return keys;
}

inline ProtectKeyList KeysUnderThePublicKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kAuthorEntity, kAuthorPublicKey, kAuthorKey));
  return keys;
}

inline std::string EncryptedUnderNames(const std::string& src) {
  return EncryptEnvelopes(src, {}, BothEntitiesKeys());
}

inline std::string EncryptedUnderThePublicKey(const std::string& src) {
  return EncryptEnvelopes(src, {}, KeysUnderThePublicKey());
}

inline std::string Design(std::string_view statement) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(statement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

inline std::string SealedModel() {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect author=\"").append(kSealerEntity).append("\"\n");
  text.append("`pragma protect data_method=\"").append(kSealerMethod);
  text.append("\"\n");
  text.append("`pragma protect data_keyowner=\"").append(kSealerEntity);
  text.append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(kSealerKeyName);
  text.append("\"\n");
  text.append("`pragma protect data_block\n").append(kSealedBlockMarker);
  text.push_back('\n');
  text.append("`pragma protect end_protected\n");
  return text;
}

inline std::string SealedModelNamingItsOwnKeys() {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect author=\"").append(kSealerEntity).append("\"\n");
  text.append("`pragma protect data_keyowner=\"").append(kSealerEntity);
  text.append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(kSealerKeyName);
  text.append("\"\n");
  text.append("`pragma protect end_protected\n");
  return text;
}

inline std::string PublicKeyDesignation() {
  std::string text = "`pragma protect data_public_key\n";
  text.append(kAuthorPublicKey).append("\n");
  return text;
}

inline std::string NamedRegionAround(std::string_view sealed) {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect author=\"").append(kAuthorEntity).append("\"\n");
  text.append("`pragma protect data_keyowner=\"").append(kAuthorEntity);
  text.append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(kAuthorKeyName);
  text.append("\"\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(sealed);
  text.append("`pragma protect end\n");
  return text;
}

inline std::string UnnamedRegionAround(std::string_view sealed) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(sealed);
  text.append("`pragma protect end\n");
  return text;
}

inline std::string RegionDesignatingItsKeyByPublicKey(
    std::string_view designation) {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect data_keyowner=\"").append(kAuthorEntity);
  text.append("\"\n");
  text.append("`pragma protect encoding=(enctype=\"raw\")\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(designation);
  text.append("`pragma protect end\n");
  return text;
}

inline std::string Without(const std::string& written,
                           const std::string& line) {
  size_t at = written.find(line);
  if (at == std::string::npos) return written;
  std::string shortened(written);
  shortened.erase(at, line.size());
  return shortened;
}
