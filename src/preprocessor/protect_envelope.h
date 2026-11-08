#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"

namespace delta {

inline constexpr std::string_view kProtectPragmaName = "protect";

enum class EnvelopeMode : std::uint8_t {
  kEncryption,
  kDecryption,
};

inline constexpr std::string_view kBeginEncryptionKeyword = "begin";

inline constexpr std::string_view kEndEncryptionKeyword = "end";

bool OpensEncryptionEnvelope(std::string_view keyword, bool has_value);

bool ClosesEncryptionEnvelope(std::string_view keyword, bool has_value);

inline constexpr std::string_view kBeginDecryptionKeyword = "begin_protected";

bool OpensDecryptionEnvelope(std::string_view keyword, bool has_value);

inline constexpr std::string_view kEndDecryptionKeyword = "end_protected";

bool ClosesDecryptionEnvelope(std::string_view keyword, bool has_value);

struct ProtectedEnvelope {
  EnvelopeMode mode;
  SourceLoc begin_loc;
  SourceLoc end_loc;
  std::vector<std::string> envelope_keywords;
  std::vector<std::string> content_keywords;
};

class ProtectEnvelopeState {
 public:
  static constexpr size_t kMinNestedDecryptionEnvelopes = 8;
  static constexpr size_t kNestedDecryptionEnvelopeLimit = 64;
  static_assert(kNestedDecryptionEnvelopeLimit >=
                kMinNestedDecryptionEnvelopes);

  bool Apply(std::string_view keyword, SourceLoc loc);

  const std::vector<ProtectedEnvelope>& OpenEnvelopes() const {
    return open_envelopes_;
  }
  const std::vector<ProtectedEnvelope>& ClosedEnvelopes() const {
    return closed_envelopes_;
  }
  const std::vector<std::string>& PendingEnvelopeKeywords() const {
    return pending_envelope_keywords_;
  }

  size_t EncryptionEnvelopeDepth() const;
  size_t DecryptionEnvelopeDepth() const;
  bool InProtectedRegion() const;

 private:
  bool Open(EnvelopeMode mode, SourceLoc loc);
  void Close(EnvelopeMode mode, SourceLoc loc);
  size_t DepthOf(EnvelopeMode mode) const;

  std::vector<ProtectedEnvelope> open_envelopes_;
  std::vector<ProtectedEnvelope> closed_envelopes_;
  std::vector<std::string> pending_envelope_keywords_;
};

}  // namespace delta
