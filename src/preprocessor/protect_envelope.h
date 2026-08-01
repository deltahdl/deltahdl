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

// The pragma keyword that opens an envelope for encryption. §34.5.1.1 gives
// its syntax as this word and nothing beside it.
inline constexpr std::string_view kBeginEncryptionKeyword = "begin";

// The pragma keyword that closes an envelope for encryption. §34.5.2.1 gives
// its syntax as this word standing alone, as §34.5.1.1 does for the word that
// opens such an envelope.
//
// One word, so one spelling of it here: everything acting on the closing word
// -- the state below, and the transformation that replaces an envelope with
// one for decryption -- reads it from this constant, so no reader can come to
// hold a spelling the others do not.
inline constexpr std::string_view kEndEncryptionKeyword = "end";

// Whether a pragma expression opens an encryption envelope: `keyword` names
// the expression, and `has_value` says whether a pragma_value was written
// against that name.
//
// §22.5.1 gives a pragma expression two spellings -- the pragma_keyword
// standing on its own, and the pragma_keyword with a pragma_value written
// against it -- and §34.5.1.1 defines the opening expression with the first of
// those alone. A value written against the word therefore leaves an expression
// that opens nothing. It is also worth a caller's saying so, because the word
// it names is one of the reserved ones and the spelling it was written in is
// not one the standard defines for that word, which no other keyword's
// definition covers either.
bool OpensEncryptionEnvelope(std::string_view keyword, bool has_value);

// Whether a pragma expression closes an encryption envelope: `keyword` names
// the expression, and `has_value` says whether a pragma_value was written
// against that name.
//
// §34.5.2.1 writes the closing expression as the word standing on its own,
// which is the first of the two spellings §22.5.1 gives a pragma expression.
// The same word with a pragma_value written against it is therefore that
// expression in a spelling it is not defined with, and it closes nothing.
//
// The two readings of a source text that act on this word -- the one that
// follows the envelopes a text opens and closes, and the one that replaces an
// encryption envelope with a decryption envelope -- ask the question here
// rather than each testing the name for itself, so neither can come to accept a
// spelling the other turns away. Their agreeing matters more here than at the
// opening word: a reading that closed a region the other left open would seal
// text the author wrote outside it, or leave sealed text the author wrote
// inside.
bool ClosesEncryptionEnvelope(std::string_view keyword, bool has_value);

// The pragma keyword that opens an envelope for decryption. §34.5.3.1 gives
// its syntax as this word standing alone, as §34.5.1.1 and §34.5.2.1 do for
// the pair delimiting an envelope for encryption.
//
// Two readings of a source text look for this word, and they look for it by
// different means: one reads the expressions out of a directive's tokens, and
// one walks the characters of a line on the encrypting side to find where a
// model that was protected already begins. One spelling here is what keeps
// them from disagreeing about where such a model starts -- a disagreement that
// would have one of them interpret, as description of the encryption it is
// running, pragma expressions belonging to somebody else's envelope.
inline constexpr std::string_view kBeginDecryptionKeyword = "begin_protected";

// Whether a pragma expression opens a decryption envelope: `keyword` names the
// expression, and `has_value` says whether a pragma_value was written against
// that name.
//
// §34.5.3.1 defines the opening expression as the pragma_keyword standing on
// its own, which is the first of the two spellings §22.5.1 gives a pragma
// expression. The same word with a pragma_value written against it is that
// expression in a spelling the standard does not define for it, and it opens
// nothing.
//
// What turns on the answer is which text is protected. A word taken as opening
// a region that the standard does not have open it would put the lines after
// it inside somebody else's envelope: their pragma expressions would be read
// as description rather than as the cleartext they are, and the text would be
// searched for a closing word that was never written. A word not taken where
// the standard does open one leaves an encrypted model's own description in
// effect over the encryption running around it. Both are worth a caller's
// saying so, the word being one of the reserved ones.
bool OpensDecryptionEnvelope(std::string_view keyword, bool has_value);

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
