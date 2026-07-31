#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"

namespace delta {

// §34.2 reserves one pragma name for describing protected envelopes: every
// piece of information that identifies an envelope is introduced by a pragma
// carrying this name, and a pragma named anything else says nothing about
// envelopes at all.
inline constexpr std::string_view kProtectPragmaName = "protect";

// The two modes of processing an envelope may be defined for. An encryption
// envelope marks a region of cleartext that is to be encrypted; a decryption
// envelope marks a region of ciphertext that is to be decrypted.
enum class EnvelopeMode : std::uint8_t {
  kEncryption,
  kDecryption,
};

// One protected envelope, together with the pragma expressions that describe
// it. `end_loc` stays invalid until a closing expression is paired with the
// opening one, so an entry with an invalid end is an envelope still open.
//
// The keywords ride on the envelope rather than on the file because that is
// the scope §34.2 gives them: an expression written ahead of an opening
// expression describes the envelope that opening expression goes on to open,
// and an expression written inside a region describes the content of that
// region, not of whichever other envelope the file happens to contain. Two
// envelopes in one source text therefore keep their descriptions apart.
struct ProtectedEnvelope {
  EnvelopeMode mode;
  SourceLoc begin_loc;
  SourceLoc end_loc;
  std::vector<std::string> envelope_keywords;
  std::vector<std::string> content_keywords;
};

// Accumulates the protected envelopes that a source text's protect pragma
// expressions open and close, in the left-to-right order those expressions are
// written. A run of expressions means the same thing however it is distributed
// over directives, so one of these follows a whole source text rather than a
// single directive.
class ProtectEnvelopeState {
 public:
  // How deeply decryption envelopes may nest is left to the implementation,
  // but §34.2 puts a floor under it: at least this many nested decryption
  // envelopes are processed.
  static constexpr size_t kMinNestedDecryptionEnvelopes = 8;
  // The depth this implementation supports, which honors that floor.
  static constexpr size_t kNestedDecryptionEnvelopeLimit = 64;
  static_assert(kNestedDecryptionEnvelopeLimit >=
                kMinNestedDecryptionEnvelopes);

  // Applies one pragma expression, named by its pragma_keyword, written at the
  // directive location `loc`. Returns false when the keyword asks to open a
  // decryption envelope nested deeper than kNestedDecryptionEnvelopeLimit,
  // which is the one condition the caller has to report.
  bool Apply(std::string_view keyword, SourceLoc loc);

  // The envelopes whose opening expression has not been paired yet, outermost
  // first.
  const std::vector<ProtectedEnvelope>& OpenEnvelopes() const {
    return open_envelopes_;
  }
  // The envelopes that have been closed, in the order they were closed.
  const std::vector<ProtectedEnvelope>& ClosedEnvelopes() const {
    return closed_envelopes_;
  }
  // Keywords written where no envelope is open. They describe the envelope the
  // next opening expression opens, so they are held here until there is an
  // envelope to hand them to.
  const std::vector<std::string>& PendingEnvelopeKeywords() const {
    return pending_envelope_keywords_;
  }

  size_t EncryptionEnvelopeDepth() const;
  size_t DecryptionEnvelopeDepth() const;
  // Code enclosed by a decryption envelope is protected code. An encryption
  // envelope encloses cleartext, so it does not protect what it encloses.
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
