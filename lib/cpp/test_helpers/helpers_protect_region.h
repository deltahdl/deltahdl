#pragma once

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_diagnosed.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

inline constexpr std::string_view kKeyOwner = "acme";
inline constexpr std::string_view kKeyName = "acme-2026";
inline constexpr std::string_view kRegionKey = "acme-region-exchange-key";

inline constexpr std::string_view kSealedDesign =
    "module sealed_m; endmodule\n";

inline constexpr std::string_view kBlockOpening =
    "`pragma protect data_block\n";

inline constexpr std::string_view kBeginProtected =
    "`pragma protect begin_protected\n";
inline constexpr std::string_view kEndProtected =
    "`pragma protect end_protected\n";

inline ProtectKeyList TheRegionsKey() {
  ProtectKeyList held;
  held.Add(
      {std::string(kKeyOwner), std::string(kKeyName), std::string(kRegionKey)});
  return held;
}

inline ProtectKeyList AKeyUnderAnotherName() {
  ProtectKeyList held;
  held.Add(
      {std::string(kKeyOwner), "some-other-key-name", std::string(kRegionKey)});
  return held;
}

inline std::string DesignatesTheProvider() {
  std::string written = "`pragma protect data_keyowner=\"";
  written.append(kKeyOwner).append("\"\n");
  return written;
}

inline std::string DesignatesTheKey() {
  std::string written = "`pragma protect data_keyname=\"";
  written.append(kKeyName).append("\"\n");
  return written;
}

inline std::string ReachesTheKey() {
  return DesignatesTheProvider() + DesignatesTheKey();
}

inline std::string RegionAround(std::string_view inside) {
  std::string written = "`pragma protect begin\n";
  written.append(inside).append("`pragma protect end\n");
  return written;
}

inline std::string RegionBody(std::string_view written) {
  std::string inside = ReachesTheKey();
  inside.append(written).append(kSealedDesign);
  return inside;
}

inline std::string RegionWriting(std::string_view written) {
  return RegionAround(RegionBody(written));
}

inline std::string Encrypted(std::string_view source) {
  return EncryptEnvelopes(source, "", TheRegionsKey());
}

inline std::string EncryptedWithoutTheKey(std::string_view source) {
  return EncryptEnvelopes(source, "", AKeyUnderAnotherName());
}

inline std::string DataBlockOf(std::string_view envelope) {
  size_t opens = envelope.find(kBlockOpening);
  if (opens == std::string_view::npos) return {};
  size_t from = opens + kBlockOpening.size();
  size_t to = envelope.find('\n', from);
  if (to == std::string_view::npos) to = envelope.size();
  return std::string(envelope.substr(from, to - from));
}

inline std::string OpenedBlockOf(std::string_view envelope) {
  std::string recovered;
  if (!DecryptProtectedRegion(DataBlockOf(envelope), kRegionKey, &recovered)) {
    return {};
  }
  return recovered;
}

inline std::string OpenedBlockWriting(std::string_view written) {
  return OpenedBlockOf(Encrypted(RegionWriting(written)));
}

struct ReadWithTheKeys {
  static PreprocConfig ConfigHoldingTheKeys() {
    PreprocConfig config;
    config.protect_keys = TheRegionsKey();
    return config;
  }

  SourceManager sources;
  DiagEngine diags{sources};
  Diagnosed diagnosed{diags};
  Preprocessor reader;
  std::string produced;

  explicit ReadWithTheKeys(const std::string& src)
      : reader(sources, diags, ConfigHoldingTheKeys()) {
    produced = reader.Preprocess(sources.AddFile("<test>", src));
  }

  size_t StillOpen() const {
    return reader.ProtectEnvelopes().DecryptionEnvelopeDepth();
  }
  size_t Closed() const {
    return reader.ProtectEnvelopes().ClosedEnvelopes().size();
  }

  bool Produced(std::string_view what) const {
    return produced.find(what) != std::string::npos;
  }
};
