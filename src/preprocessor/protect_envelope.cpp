#include "preprocessor/protect_envelope.h"

#include <algorithm>
#include <cstddef>
#include <iterator>
#include <string_view>
#include <utility>
#include <vector>

#include "common/source_loc.h"

namespace delta {

bool OpensEncryptionEnvelope(std::string_view keyword, bool has_value) {
  return keyword == kBeginEncryptionKeyword && !has_value;
}

bool ClosesEncryptionEnvelope(std::string_view keyword, bool has_value) {
  return keyword == kEndEncryptionKeyword && !has_value;
}

bool OpensDecryptionEnvelope(std::string_view keyword, bool has_value) {
  return keyword == kBeginDecryptionKeyword && !has_value;
}

bool ClosesDecryptionEnvelope(std::string_view keyword, bool has_value) {
  return keyword == kEndDecryptionKeyword && !has_value;
}

size_t ProtectEnvelopeState::DepthOf(EnvelopeMode mode) const {
  return static_cast<size_t>(
      std::count_if(open_envelopes_.begin(), open_envelopes_.end(),
                    [mode](const ProtectedEnvelope& envelope) {
                      return envelope.mode == mode;
                    }));
}

size_t ProtectEnvelopeState::EncryptionEnvelopeDepth() const {
  return DepthOf(EnvelopeMode::kEncryption);
}

size_t ProtectEnvelopeState::DecryptionEnvelopeDepth() const {
  return DepthOf(EnvelopeMode::kDecryption);
}

bool ProtectEnvelopeState::InProtectedRegion() const {
  return DepthOf(EnvelopeMode::kDecryption) > 0;
}

bool ProtectEnvelopeState::Open(EnvelopeMode mode, SourceLoc loc) {
  if (mode == EnvelopeMode::kDecryption &&
      DepthOf(mode) >= kNestedDecryptionEnvelopeLimit) {
    return false;
  }
  ProtectedEnvelope envelope;
  envelope.mode = mode;
  envelope.begin_loc = loc;
  envelope.envelope_keywords = std::move(pending_envelope_keywords_);
  pending_envelope_keywords_.clear();
  open_envelopes_.push_back(std::move(envelope));
  return true;
}

void ProtectEnvelopeState::Close(EnvelopeMode mode, SourceLoc loc) {
  auto it = std::find_if(open_envelopes_.rbegin(), open_envelopes_.rend(),
                         [mode](const ProtectedEnvelope& envelope) {
                           return envelope.mode == mode;
                         });
  if (it == open_envelopes_.rend()) return;
  ProtectedEnvelope envelope = std::move(*it);
  envelope.end_loc = loc;
  closed_envelopes_.push_back(std::move(envelope));
  open_envelopes_.erase(std::prev(it.base()));
}

bool ProtectEnvelopeState::Apply(std::string_view keyword, SourceLoc loc) {
  if (keyword == kBeginEncryptionKeyword) {
    return Open(EnvelopeMode::kEncryption, loc);
  }
  if (keyword == kBeginDecryptionKeyword) {
    return Open(EnvelopeMode::kDecryption, loc);
  }
  if (keyword == kEndEncryptionKeyword) {
    Close(EnvelopeMode::kEncryption, loc);
    return true;
  }
  if (keyword == kEndDecryptionKeyword) {
    Close(EnvelopeMode::kDecryption, loc);
    return true;
  }
  if (open_envelopes_.empty()) {
    pending_envelope_keywords_.emplace_back(keyword);
  } else {
    open_envelopes_.back().content_keywords.emplace_back(keyword);
  }
  return true;
}

}  // namespace delta
