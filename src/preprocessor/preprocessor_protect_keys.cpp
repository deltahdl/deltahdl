#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

namespace delta {
namespace {

// Whether the expression designates one of the keys of the entity that
// provided the keys a protected region's own keys are under.
//
// A designation is a value written against one of the two names that pick such
// a key out. An expression with nothing written against it picks out nothing,
// and neither does one whose value is a parenthesized list of further
// expressions, those qualifying a value rather than being one.
bool DesignatesKeyBlockKey(const PragmaKeywordExpression& expr) {
  if (!expr.has_value || expr.value.empty()) return false;
  return IsProtectKeyBlockDesignationKeyword(expr.keyword);
}

// Whether the expression is the one §34.5.26.1 defines: the keyword announcing
// a public key, standing alone. The same name carrying a pragma_value is that
// expression written in a spelling it is not defined with, and announces
// nothing about the line beneath it.
bool AnnouncesPublicKey(const PragmaKeywordExpression& expr) {
  return expr.keyword == kKeyPublicKeyKeyword && !expr.has_value;
}

// Whether the expression is the one §34.5.27.1 defines: the keyword announcing
// a key block, standing alone. The block it announces begins on the line after
// it, so the same name carrying a pragma_value announces nothing about that
// line, having been written in a spelling the keyword is not defined with.
bool AnnouncesKeyBlock(const PragmaKeywordExpression& expr) {
  return expr.keyword == kKeyBlockKeyword && !expr.has_value;
}

// The same for §34.5.14.1's keyword, which is defined in the same shape and
// speaks for the line after it in the same way: the encoded value of the key
// that opens the region's data block is written there.
bool AnnouncesDataDecryptKey(const PragmaKeywordExpression& expr) {
  return expr.keyword == kDataDecryptKeyKeyword && !expr.has_value;
}

// The same for §34.5.13.1's keyword, whose line holds the encoded value of the
// public key the region's data are under. The same name carrying a pragma_value
// is that expression written in a spelling it is not defined with, and
// announces nothing about the line beneath it.
bool AnnouncesDataPublicKey(const PragmaKeywordExpression& expr) {
  return expr.keyword == kDataPublicKeyKeyword && !expr.has_value;
}

// The same for §34.5.19.1's keyword, whose line holds the encoded value of the
// public key the region's digest is under. The same name carrying a
// pragma_value is that expression written in a spelling it is not defined with,
// and announces nothing about the line beneath it.
bool AnnouncesDigestPublicKey(const PragmaKeywordExpression& expr) {
  return expr.keyword == kDigestPublicKeyKeyword && !expr.has_value;
}

// The same for §34.5.20.1's keyword, which speaks for the line after it in the
// same way: the encoded value of the key that opens the region's digest block
// is written there.
bool AnnouncesDigestDecryptKey(const PragmaKeywordExpression& expr) {
  return expr.keyword == kDigestDecryptKeyKeyword && !expr.has_value;
}

// And for §34.5.22.1's, whose line holds the digest the block above it is
// checked against. The same name carrying a pragma_value announces nothing
// about that line, having been written in a spelling the keyword is not defined
// with.
bool AnnouncesDigestBlock(const PragmaKeywordExpression& expr) {
  return expr.keyword == kDigestBlockKeyword && !expr.has_value;
}

// And for §34.5.15.1's, whose line the block holding the region's design begins
// on. The same name carrying a pragma_value announces nothing about that line,
// having been written in a spelling the keyword is not defined with.
bool AnnouncesDataBlock(const PragmaKeywordExpression& expr) {
  return expr.keyword == kDataBlockKeyword && !expr.has_value;
}

}  // namespace

// §34.5.23 puts on the entity that provided the keys a region's own keys are
// under the constraints §34.5.10 states for the entity whose keys the data are
// under. What those constraints govern is the values designating one of that
// entity's keys: one value written under a single entity against both of the
// names that designate a key would have to pick out two of its keys at once,
// so it picks out neither, and it is reported.
//
// The entity is what the values are unique for. The same value written under
// two entities is two designations rather than one repeated, each being read
// against a different list of keys, and it stands. For the same reason these
// designations are held apart from the ones written for the entity whose keys
// the data are under: those are unique for that entity, and a value serving
// both entities has repeated nothing.
//
// §34.5.26 adds what the two designations may not do even where each is
// unique. A text writing both has picked out one key twice, so two
// designations reaching two different keys of the entity leave the region with
// no single key to be under. That is only decided where the tool holds a key
// under each of them; where it does not, there is no pair of keys to differ,
// and what the text wrote stands.
void Preprocessor::CheckKeyBlockDesignation(std::string_view keyword,
                                            std::string_view value,
                                            SourceLoc loc) {
  if (value.empty()) return;
  ProtectKeywordValue owner = protect_keywords_.ValueOf(kKeyKeyownerKeyword);
  if (!protect_key_block_designations_.Record(owner.value, keyword, value)) {
    diag_.Error(loc,
                "protect pragma writes one value against both of the names "
                "that designate a key of the key_keyowner in effect",
                Subclause("34.5.23"));
  }
  if (ProtectKeyBlockDesignationsAgree(protect_keywords_,
                                       config_.protect_keys) ==
      ProtectKeyAgreement::kDifferentKeys) {
    diag_.Error(loc,
                "protect pragma key_public_key and key_keyname designate "
                "different keys of the key_keyowner in effect",
                Subclause("34.5.26"));
  }
}

// The announcement §34.5.26.1 makes is acted on after the designation this
// expression carries, because what it says concerns the line after this one
// rather than this expression: the keyword standing alone leaves the encoded
// value of a public key to be read from the next line of the file.
void Preprocessor::ApplyKeyBlockKeywords(const PragmaKeywordExpression& expr,
                                         SourceLoc loc) {
  if (DesignatesKeyBlockKey(expr)) {
    CheckKeyBlockDesignation(expr.keyword, ProtectPragmaValueBody(expr.value),
                             loc);
  }
  if (AnnouncesPublicKey(expr) && protect_envelopes_.InProtectedRegion()) {
    key_public_key_value_next_ = true;
  }
}

// §34.5.27 has a key block begin on the line after the keyword announcing it,
// §34.5.14 has the encoded value of the data key written on the line after the
// keyword carrying it, §34.5.13 has the encoded value of the public key those
// data are under written the same way, §34.5.19 has the encoded value of the
// public key the region's digest is under written the same way again, §34.5.20
// has the key that opens the region's digests written the same way once more,
// and §34.5.22 has the digest itself output on the line following the keyword
// announcing it. All six speak for the next line rather than for their own, so
// all six are recorded here and acted on once that line arrives.
//
// Only an announcement inside a decryption envelope is read this way. One there
// is what an encrypting tool wrote into a protected block along with the value
// beneath it, which is the arrangement every one of those subclauses has that
// tool produce. Outside every envelope there is no protected block for a key to
// have been made for or a digest to have been generated over, so the line
// beneath the announcement is text of the source like any other and is left to
// whatever reads it.
void Preprocessor::ApplyAnnouncedBlockKeywords(
    const PragmaKeywordExpression& expr) {
  if (!protect_envelopes_.InProtectedRegion()) return;
  if (AnnouncesKeyBlock(expr)) key_block_value_next_ = true;
  if (AnnouncesDataDecryptKey(expr)) data_decrypt_key_value_next_ = true;
  if (AnnouncesDataPublicKey(expr)) data_public_key_value_next_ = true;
  if (AnnouncesDigestPublicKey(expr)) digest_public_key_value_next_ = true;
  if (AnnouncesDigestDecryptKey(expr)) digest_decrypt_key_value_next_ = true;
  if (AnnouncesDataBlock(expr)) data_block_value_next_ = true;
  // §34.5.22 has a digest block immediately follow the key block or data block
  // whose digest it holds, so an expression standing anywhere else holds the
  // digest of nothing and announces nothing about the line beneath it. That
  // line is then read as whatever it is: a design carrying the request
  // expression that asked for these digests in the first place is put back with
  // the expression still in it, and the line after that expression is design.
  if (AnnouncesDigestBlock(expr) && !digest_target_.cleartext.empty()) {
    digest_block_value_next_ = true;
  }
}

// §34.5.13 has the name given to the key a region's data are under and the
// public key that key is refer to one key wherever a region wrote both. The two
// are alternative ways of picking one key out of one entity's list rather than
// two keys to be under at once, so a region whose designations reach different
// keys of that entity has left its data with no single key to be read under.
//
// It is only decided where the tool holds a key under each designation. With
// one of them reaching nothing there is no second key for the first to disagree
// with, and a tool that was given no keys at all has nothing to compare, so in
// both cases what the region wrote stands.
void Preprocessor::CheckDataDesignationAgreement(SourceLoc loc) {
  if (ProtectDataDesignationsAgree(protect_keywords_, config_.protect_keys) !=
      ProtectKeyAgreement::kDifferentKeys) {
    return;
  }
  diag_.Error(loc,
              "protect pragma data_public_key and data_keyname designate "
              "different keys of the data_keyowner in effect",
              Subclause("34.5.13"));
}

// §34.5.19 has the name given to the key a region's digest is under and the
// public key that key is refer to one key wherever a region wrote both. The two
// are alternative ways of picking one key out of one entity's list rather than
// two keys to be under at once, so a region whose designations reach different
// keys of that entity has left its digest with no single key to be read under.
//
// It is only decided where the tool holds a key under each designation. With
// one of them reaching nothing there is no second key for the first to
// disagree with, and a tool that was given no keys at all has nothing to
// compare, so in both cases what the region wrote stands.
void Preprocessor::CheckDigestDesignationAgreement(SourceLoc loc) {
  if (ProtectDigestDesignationsAgree(protect_keywords_, config_.protect_keys) !=
      ProtectKeyAgreement::kDifferentKeys) {
    return;
  }
  diag_.Error(loc,
              "protect pragma digest_public_key and digest_keyname designate "
              "different keys of the digest_keyowner in effect",
              Subclause("34.5.19"));
}

// Whether `expr` names one of the reserved words that delimit a protected
// envelope in the other of the two spellings §22.5.1 gives a pragma
// expression, having reported it where it does.
//
// Each of those words is defined as the pragma_keyword standing on its own --
// §34.5.1.1 and §34.5.2.1 for the pair marking a region to be encrypted, and
// §34.5.3.1 and §34.5.4.1 for the pair marking where a region encrypted already
// starts and stops -- so the same word carrying a pragma_value marks nothing.
// Which text is protected is what the unmarked boundary decides, so an author
// is told, rather than left to find their design in the wrong half of an
// envelope with nothing pointing at the word that put it there.
bool Preprocessor::ReportDelimiterWrittenWithValue(
    const PragmaKeywordExpression& expr, SourceLoc loc) {
  if (expr.keyword == kBeginEncryptionKeyword &&
      !OpensEncryptionEnvelope(expr.keyword, expr.has_value)) {
    diag_.Error(loc,
                "protect pragma begin keyword is written on its own and "
                "takes no pragma_value",
                Subclause("34.5.1.1"));
    return true;
  }
  if (expr.keyword == kEndEncryptionKeyword &&
      !ClosesEncryptionEnvelope(expr.keyword, expr.has_value)) {
    diag_.Error(loc,
                "protect pragma end keyword is written on its own and takes "
                "no pragma_value",
                Subclause("34.5.2.1"));
    return true;
  }
  if (expr.keyword == kBeginDecryptionKeyword &&
      !OpensDecryptionEnvelope(expr.keyword, expr.has_value)) {
    diag_.Error(loc,
                "protect pragma begin_protected keyword is written on its own "
                "and takes no pragma_value",
                Subclause("34.5.3.1"));
    return true;
  }
  if (expr.keyword == kEndDecryptionKeyword &&
      !ClosesDecryptionEnvelope(expr.keyword, expr.has_value)) {
    diag_.Error(loc,
                "protect pragma end_protected keyword is written on its own "
                "and takes no pragma_value",
                Subclause("34.5.4.1"));
    return true;
  }
  return false;
}

// Hands the protect pragma's expressions to the envelope state one at a time,
// in the order they were written. The state carries from one directive to the
// next, so the same run of expressions leaves the same envelopes behind
// whether it was written as one directive or spread over several.
//
// No text comes back from here. §34.5.15.1 spells the expression carrying a
// region as the keyword standing alone, and §34.5.15.2 has the block begin on
// the line beneath it, so the design a region records is recovered by
// Preprocessor::TakeDataBlockValue when that line arrives rather than by any
// expression this reads. What an expression here does is record that the
// keyword was written, which ApplyAnnouncedBlockKeywords does for all eight
// keywords whose definitions speak for the line after them.
void Preprocessor::ApplyProtectKeywords(
    const std::vector<PragmaKeywordExpression>& keywords, SourceLoc loc) {
  for (const PragmaKeywordExpression& expr : keywords) {
    // A reserved word that delimits an envelope, written in a spelling it is
    // not defined with, delimits nothing: nothing is put in effect for it and
    // no envelope opens or closes on it.
    if (ReportDelimiterWrittenWithValue(expr, loc)) continue;
    // §34.5.31.2 defines this one expression by naming another that already
    // does what it does: it is a synonym for a reset pragma directive naming
    // protect in its keyword list, so it is answered by the same call that
    // directive is answered by and the two spellings restore the same things.
    //
    // §34.5.31.1 writes the keyword standing alone, so a value written against
    // it is not the expression the subclause defines and restores nothing. It
    // goes on to be applied like any other keyword written in a spelling no
    // subclause defines, which is what §34.4 does with the value written
    // against a name its table lists.
    //
    // It is answered before the expression is applied so that the keyword
    // putting the values back does not leave one of its own standing.
    if (expr.keyword == kResetKeyword && !expr.has_value) {
      ResetPragma(kProtectPragmaName);
      continue;
    }
    // Whatever the expression goes on to do to the envelopes, §34.4 puts the
    // value it writes against a reserved keyword in effect from here on: the
    // scope is the text after this point, not the envelope, the declaration or
    // the file. A keyword whose value is a list of further expressions has that
    // list put in effect for it -- §34.5.9.1 defines its keyword that way, and
    // what a later reading needs from it is written nowhere else.
    //
    // An expression that is a keyword and nothing else writes no value, so it
    // puts none in effect and the keyword is left where it stood. §34.5.13.1,
    // §34.5.14.1, §34.5.20.1 and §34.5.26.1 define their keywords that way, and
    // so do §34.5.1.1 through §34.5.4.1 for the delimiters, and each of the
    // first four announces a value on the line beneath it rather than carrying
    // one: the value arrives at Preprocessor::TakeDataPublicKeyValue and the
    // three beside it, which put it in effect when the line is read. Recording
    // an entry here would leave the keyword stating an empty value in the
    // meantime, which ProtectKeywordValue::defaulted
    // (preprocessor/protect_keywords.h) exists to tell from a keyword no
    // directive has written, and the announcement would be read as a
    // designation of nothing rather than as a designation not yet made.
    //
    // The parenthesized form is written with a value all the same, having an
    // '=' before it, so §34.5.9.1's encoding still takes effect.
    if (expr.has_value) {
      protect_keywords_.Apply(
          expr.keyword, expr.value.empty() ? expr.value_list : expr.value);
    }
    if (!protect_envelopes_.Apply(expr.keyword, loc)) {
      diag_.Error(loc,
                  "protect pragma nests decryption envelopes more deeply than "
                  "this implementation processes",
                  Subclause::None());
      continue;
    }
    // §34.5.4.2 ends the run of gathered pragmas at the closing expression. It
    // is ended here as well as at the line reader: one directive may open a
    // designation and close the envelope in that order, and only the
    // expressions record which of the two was written first.
    if (ClosesDecryptionEnvelope(expr.keyword, expr.has_value)) {
      EndAccumulatedProtectPragmas();
    }
    CheckDataKeyname(expr, loc);
    CheckDigestKeyname(expr, loc);
    CheckKeyKeyname(expr, loc);
    CheckKeyDesignation(expr, loc);
    CheckDigestDesignation(expr, loc);
    ApplyKeyBlockKeywords(expr, loc);
    ApplyAnnouncedBlockKeywords(expr);
    ApplyViewport(expr, loc);
  }
}

}  // namespace delta
