#include <string_view>

#include "common/diagnostic.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"

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
                "that designate a key of the key_keyowner in effect");
  }
  if (ProtectKeyBlockDesignationsAgree(protect_keywords_,
                                       config_.protect_keys) ==
      ProtectKeyAgreement::kDifferentKeys) {
    diag_.Error(loc,
                "protect pragma key_public_key and key_keyname designate "
                "different keys of the key_keyowner in effect");
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

// §34.5.26: the keyword announcing a public key says that the next line of the
// file holds that key's encoded value, so the line is the designation of a key
// rather than a line of the design, and it is read as the value the keyword
// was left waiting for. Being a designation, it is held to what §34.5.23 and
// §34.5.26 require of one, exactly as a designation written against a keyword
// is.
//
// The value is taken as the line was written, without the whitespace that
// positioned it. §34.5.26 has it encoded as the encoding pragma expression in
// effect specifies, and this implementation writes and reads a single encoding
// and re-encodes nothing on the way through, so what the line carries is the
// value as it stands.
//
// Only a line inside a decryption envelope is read this way. An announcement
// there is one an encrypting tool wrote into a protected block along with the
// value beneath it, which is the arrangement §34.5.26 has that tool produce.
// Outside every envelope there is no protected block for a public key to have
// been used for, so the text beneath the announcement is text of the source
// like any other and is left to whatever reads it.
bool Preprocessor::TakeKeyPublicKeyValue(std::string_view line, SourceLoc loc) {
  if (!key_public_key_value_next_) return false;
  key_public_key_value_next_ = false;
  std::string_view value = Trim(line);
  protect_keywords_.Apply(kKeyPublicKeyKeyword, value);
  CheckKeyBlockDesignation(kKeyPublicKeyKeyword, value, loc);
  return true;
}

}  // namespace delta
