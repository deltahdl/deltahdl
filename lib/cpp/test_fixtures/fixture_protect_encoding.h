#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

inline constexpr std::string_view kEncodingExchangeKey = "globex-exchange-key";

inline constexpr std::string_view kEncodingSealedDesign =
    "module sealed_m; endmodule\n";

inline constexpr std::string_view kSecondDesign =
    "module sealed_n; endmodule\n";

inline constexpr std::string_view kAwkwardDesign =
    "module sealed_q; // \" \x02\nendmodule\n";

inline constexpr std::string_view kEncodingBlockOpening =
    "`pragma protect data_block\n";

inline constexpr std::string_view kProtectedOpening =
    "`pragma protect begin_protected";

inline constexpr std::string_view kDataPublicKeyLine =
    "`pragma protect data_public_key\n";
inline constexpr std::string_view kKeyPublicKeyLine =
    "`pragma protect key_public_key\n";
inline constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";
inline constexpr std::string_view kDataDecryptKeyLine =
    "`pragma protect data_decrypt_key\n";

inline constexpr std::string_view kAnyEncoding = "`pragma protect encoding=";

inline constexpr std::string_view kDigestBlockLine =
    "`pragma protect digest_block\n";

inline constexpr std::string_view kKeyProvider = "acme";
inline constexpr std::string_view kProviderKey = "acme-provider-key";

inline constexpr std::string_view kDesignatedKey = "acme public";

inline constexpr std::string_view kDesignationInBase64 = "YWNtZSBwdWJsaWM=";
inline constexpr std::string_view kDesignationInUuencode = "+86-M92!P=6)L:6,`";
inline constexpr std::string_view kDesignationInQuotedPrintable =
    "acme=20public";

inline constexpr std::string_view kUnprintableDesignation = "acme\x02public";

inline constexpr std::string_view kUnprovidedEnctype = "x-nobody-provides-this";

inline std::string StatesEncoding(std::string_view list) {
  std::string directive(kAnyEncoding);
  directive.append(list).append("\n");
  return directive;
}

inline std::string NamesScheme(std::string_view enctype) {
  std::string list = "(enctype=\"";
  list.append(enctype).append("\")");
  return StatesEncoding(list);
}

inline std::string EncodingRegionBody(std::string_view inside) {
  std::string body(inside);
  body.append(kEncodingSealedDesign);
  return body;
}

inline std::string RegionHolding(std::string_view inside) {
  std::string region = "`pragma protect begin\n";
  region.append(EncodingRegionBody(inside));
  region.append("`pragma protect end\n");
  return region;
}

inline std::string TheCountOf(size_t bytes) {
  std::string counted = "bytes=";
  counted.append(std::to_string(bytes)).append(")");
  return counted;
}

inline PreprocConfig HoldingTheKey() {
  PreprocConfig config;
  config.protect_key = std::string(kEncodingExchangeKey);
  return config;
}

inline std::string EnvelopeOf(const std::string& source) {
  std::string envelope = EncryptEnvelopes(source, kEncodingExchangeKey);
  EXPECT_FALSE(Holds(envelope, kEncodingSealedDesign));
  return envelope;
}

inline std::string EnvelopeAround(std::string_view inside) {
  return EnvelopeOf(RegionHolding(inside));
}

inline std::string BlockLinesAfter(std::string_view envelope,
                                   std::string_view opening) {
  size_t opens = envelope.find(opening);
  if (opens == std::string_view::npos) return {};
  std::string_view rest = envelope.substr(opens + opening.size());
  std::string block;
  while (!rest.empty()) {
    size_t ends = rest.find('\n');
    std::string_view line =
        ends == std::string_view::npos ? rest : rest.substr(0, ends);
    if (line.rfind("`pragma", 0) == 0) break;
    if (!block.empty()) block.push_back('\n');
    block.append(line);
    if (ends == std::string_view::npos) break;
    rest.remove_prefix(ends + 1);
  }
  return block;
}

inline std::string EncodingDataBlockLinesOf(std::string_view envelope) {
  return BlockLinesAfter(envelope, kEncodingBlockOpening);
}

inline std::string EncodingDataBlockOf(std::string_view envelope) {
  size_t opens = envelope.find(kEncodingBlockOpening);
  if (opens == std::string_view::npos) return {};
  size_t from = opens + kEncodingBlockOpening.size();
  size_t to = envelope.find('\n', from);
  if (to == std::string_view::npos) to = envelope.size();
  return std::string(envelope.substr(from, to - from));
}

inline std::string ProtectedPartOf(std::string_view text) {
  size_t opens = text.find(kProtectedOpening);
  if (opens == std::string_view::npos) return {};
  return std::string(text.substr(opens));
}

inline std::string LineAfter(std::string_view text, std::string_view opening) {
  size_t stands = text.find(opening);
  if (stands == std::string_view::npos) return {};
  size_t from = stands + opening.size();
  size_t to = text.find('\n', from);
  if (to == std::string_view::npos) return {};
  return std::string(text.substr(from, to - from));
}

inline std::string EnvelopeReadUnder(std::string_view directive) {
  std::string envelope = EnvelopeAround("");
  size_t block = envelope.find(kEncodingBlockOpening);
  EXPECT_NE(block, std::string::npos);
  return envelope.insert(block, std::string(directive));
}

inline std::string EnvelopeOpeningWith(std::string_view directive) {
  std::string envelope = EnvelopeAround("");
  size_t opens = envelope.find(kProtectedOpening);
  EXPECT_NE(opens, std::string::npos);
  size_t ends = envelope.find('\n', opens);
  EXPECT_NE(ends, std::string::npos);
  return envelope.insert(ends + 1, std::string(directive));
}

inline std::string TwoRegions() {
  std::string source = "`pragma protect begin\n";
  source.append(kEncodingSealedDesign).append("`pragma protect end\n");
  source.append("`pragma protect begin\n");
  source.append(kSecondDesign).append("`pragma protect end\n");
  return source;
}

inline std::string RegionDesignatingTheDataKey(std::string_view enctype,
                                               std::string_view encoded) {
  std::string inside(NamesScheme(enctype));
  inside.append(kDataPublicKeyLine).append(encoded).append("\n");
  return RegionHolding(inside);
}

inline std::string RegionDesignating(std::string_view enctype,
                                     std::string_view encoded) {
  std::string inside = "`pragma protect key_keyowner=\"";
  inside.append(kKeyProvider).append("\"\n");
  inside.append(NamesScheme(enctype));
  inside.append("`pragma protect key_public_key\n");
  inside.append(encoded).append("\n");
  return RegionHolding(inside);
}

inline std::string SealedByDesignation(std::string_view enctype,
                                       std::string_view encoded,
                                       std::string_view held) {
  ProtectKeyList keys;
  keys.Add({std::string(kKeyProvider), std::string(held),
            std::string(kProviderKey)});
  return EncryptEnvelopes(RegionDesignating(enctype, encoded), "", keys);
}
