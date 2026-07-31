#include "preprocessor/protect_envelope.h"

#include <algorithm>
#include <cstddef>
#include <iterator>
#include <string_view>
#include <utility>
#include <vector>

#include "common/source_loc.h"

namespace delta {
namespace {

// The pragma expressions that delimit an envelope rather than describe one:
// one opens a region of text and one closes it, per mode of processing. The
// two words delimiting a region for encryption are spelled beside the
// subclauses defining them, in the header.
constexpr std::string_view kBeginDecryption = "begin_protected";
constexpr std::string_view kEndDecryption = "end_protected";

}  // namespace

bool OpensEncryptionEnvelope(std::string_view keyword, bool has_value) {
  return keyword == kBeginEncryptionKeyword && !has_value;
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

// The keywords waiting outside every region describe whichever envelope opens
// next, so opening one takes them all and leaves nothing behind for the
// envelope after it.
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

// A closing expression takes the most recent opening expression of its own
// mode that has not already been closed. Searching back for the mode rather
// than taking whatever is innermost is what lets one kind of envelope sit
// inside the other without either one's closing expression claiming the
// wrong opening. Where no such expression is open there is nothing for the
// closing one to be associated with, so it closes no envelope.
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
  if (keyword == kBeginDecryption) return Open(EnvelopeMode::kDecryption, loc);
  if (keyword == kEndEncryptionKeyword) {
    Close(EnvelopeMode::kEncryption, loc);
    return true;
  }
  if (keyword == kEndDecryption) {
    Close(EnvelopeMode::kDecryption, loc);
    return true;
  }
  // An expression written inside a region describes that region's content,
  // and the region it is written inside is the innermost one still open.
  // Outside every region it waits for the envelope it describes to open.
  if (open_envelopes_.empty()) {
    pending_envelope_keywords_.emplace_back(keyword);
  } else {
    open_envelopes_.back().content_keywords.emplace_back(keyword);
  }
  return true;
}

}  // namespace delta
