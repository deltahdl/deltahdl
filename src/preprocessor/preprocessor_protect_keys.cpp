#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_key_method.h"
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

// §34.5.27: the block a key_block expression announces is first read in the
// encoded form, the encoding is reversed, and then the block is internally
// decrypted. The resulting text is then parsed to determine the keys required
// to decrypt the data block.
//
// What a key block recovers to is protect pragma directives, so parsing it is
// running it through the same reading every directive of the source goes
// through: what those directives put in effect is what the region's data block
// is then opened with, and no second grammar has to exist for the inside of a
// block. It contributes no text of its own -- a key block holds keys rather
// than design -- so what that reading produces is dropped.
//
// The key the block itself is opened with is the one §34.5.25 and §34.5.26
// reach: the entity named for the region's own keys, combined with whichever
// designation of one of that entity's keys stands before the block. Those are
// restated ahead of each block, their scope being lexical, so an envelope
// carrying several reaches a different key for each.
//
// A block that does not open is passed over in silence. §34.5.27 has several
// key blocks stand for alternative decryption keys to one envelope, so a reader
// holding one entity's key is expected to be unable to open the blocks written
// for the others, and reporting each of those would make the ordinary case
// noisy. What no key at all costs is the data block, which says so where it is
// reached.
//
// The recovered text is read one step deeper than the text carrying it. Reading
// it is reading a source text found inside another, and bounding that the way
// an inclusion is bounded is what keeps a block whose content names a further
// block from being followed without end.
bool Preprocessor::TakeKeyBlockValue(std::string_view line, SourceLoc loc,
                                     int depth) {
  if (!key_block_value_next_) return false;
  key_block_value_next_ = false;
  std::string block;
  // A line that cannot be read out of the scheme in effect carries no block,
  // and the line is consumed either way: the keyword above it said the line is
  // key material, so it is not text of the design whether or not a block came
  // out of it.
  if (!ReadEncodedProtectValue(Trim(line), loc, &block)) return true;
  std::string content;
  if (!DecryptProtectedBlock(
          block, ProtectKeyBlockKey(protect_keywords_, config_.protect_keys),
          &content)) {
    return true;
  }
  // The block is run for what it defines and its text is appended nowhere, so
  // its lines are not lines of the output and must not be recorded as such.
  // Recording them would name lines the output does not have and would displace
  // every line written after this one.
  bool was_recording = recording_origins_;
  recording_origins_ = false;
  ProcessSource(content, loc.file_id, depth + 1);
  recording_origins_ = was_recording;
  // §34.5.22 owes this block a digest of its own, written immediately after it,
  // so what the block recovered to is held for the digest that follows. The key
  // that digest is under is read only now, because the block just read is what
  // carried it: §34.5.20 puts the digest's key inside the very block whose
  // digest is checked with it, so a reader learns the key by opening the block
  // and then checks that the block it opened is the one that was sealed.
  digest_target_ = {content, std::string(DigestBlockKeyInEffect())};
  return true;
}

// §34.5.20: a line a digest_decrypt_key expression announces holds the encoded
// value of the key that will decrypt the region's digest block, so the line is
// that key rather than a line of the design, and it is read as the value the
// keyword was left waiting for.
//
// What the line carries is the key's encoded value rather than the key, and
// §34.5.20 has that value encoded as the encoding pragma expression specifies,
// so reading it back out of the scheme in effect is what leaves the key itself
// in hand. A key travels the same whichever scheme the envelope chose to spell
// it with.
//
// A line that is not something the scheme in effect writes carries no key, and
// the region's digests are left under the key its data are under -- the default
// this subclause settles for a text that specified none. Saying so is what
// keeps a digest from being reported as one the block disagrees with when what
// really happened is that no key was recovered to check it with.
bool Preprocessor::TakeDigestDecryptKeyValue(std::string_view line,
                                             SourceLoc loc) {
  if (!digest_decrypt_key_value_next_) return false;
  digest_decrypt_key_value_next_ = false;
  std::string key;
  if (!ReadEncodedProtectValue(Trim(line), loc, &key)) return true;
  // §34.5.16.2: a decryption key recovered here is one of the three
  // designations the values of which are unique for the digest_keyowner in
  // effect, so it is held to that whether it was written against the keyword
  // or, as §34.5.20.1 writes it, on the line beneath the keyword.
  CheckDigestDesignationValue(kDigestDecryptKeyKeyword, key, loc);
  digest_decrypt_key_ = std::move(key);
  return true;
}

// §34.5.22: a line a digest_block expression announces holds the encoded value
// of the message digest of the block this one immediately follows, so the line
// is that digest rather than a line of the design, and it is read as the value
// the keyword was left waiting for.
//
// What the digest is for is authenticating the block above it: the digest the
// block carries is decrypted with the key the region named for it, a digest is
// generated from the data the reading recovered, and the two are compared. Two
// that disagree say the digest or the encrypted data was altered after the
// input data was encrypted, and which of the two it was is not something the
// comparison can tell.
//
// A digest this reader cannot open is passed over in silence. §34.5.27 has the
// key blocks of one envelope stand for alternative ways in, so a reader holding
// one entity's key is expected to be unable to open the blocks written for the
// others, and each of those is owed a digest a reader of another block has no
// business checking. Only two digests that were both reached and disagree say
// anything happened to the data.
//
// The block being checked is spent by the check, so a second digest written
// after it finds nothing to announce it rather than checking the same block
// twice.
bool Preprocessor::TakeDigestBlockValue(std::string_view line, SourceLoc loc) {
  if (!digest_block_value_next_) return false;
  digest_block_value_next_ = false;
  ProtectDigestTarget target = std::move(digest_target_);
  digest_target_ = ProtectDigestTarget();
  std::string block;
  if (!ReadEncodedProtectValue(Trim(line), loc, &block)) return true;
  last_digest_block_check_ =
      CheckProtectDigestBlock(block, target, DigestMethodInEffect());
  if (last_digest_block_check_ == ProtectDigestCheck::kAltered) {
    diag_.Error(loc,
                "protect pragma digest block disagrees with the block it "
                "follows, so one of the two was altered after encryption",
                Subclause("34.5.22"));
  }
  return true;
}

// §34.5.14: the line a data_decrypt_key expression announces holds the encoded
// value of the key that will decrypt the region's data block, so the line is
// that key rather than a line of the design, and it is read as the value the
// keyword was left waiting for.
//
// What the line carries is the key's encoded value rather than the key, and
// §34.5.9 has every encoded value of an envelope written under the coding
// scheme that envelope declares, so reading it back out of that scheme is what
// leaves the key itself in hand. A key travels the same whichever scheme the
// envelope chose to spell it with.
//
// A line that is not something the scheme in effect writes carries no key, and
// the region is left with none. Saying so is what keeps a block from being
// reported as one the supplied key does not fit when what really happened is
// that no key was recovered to try.
bool Preprocessor::TakeDataDecryptKeyValue(std::string_view line,
                                           SourceLoc loc) {
  if (!data_decrypt_key_value_next_) return false;
  data_decrypt_key_value_next_ = false;
  std::string key;
  if (!ReadEncodedProtectValue(Trim(line), loc, &key)) return true;
  // §34.5.10.2: a decryption key recovered here is one of the three
  // designations the values of which are unique for the data_keyowner in
  // effect, so it is held to that whether it was written against the keyword
  // or, as §34.5.14.1 writes it, on the line beneath the keyword.
  CheckDataKeyDesignationValue(kDataDecryptKeyKeyword, key, loc);
  data_decrypt_key_ = std::move(key);
  return true;
}

// §34.5.26: the keyword announcing a public key says that the next line of the
// file holds that key's encoded value, so the line is the designation of a key
// rather than a line of the design, and it is read as the value the keyword
// was left waiting for. Being a designation, it is held to what §34.5.23 and
// §34.5.26 require of one, exactly as a designation written against a keyword
// is.
//
// The whole of the line is the value, taken without the whitespace that
// positioned it. What the line carries is the key's encoded value rather than
// the key, and §34.5.26 sends the reading to the encoding pragma expression in
// effect for the coding scheme it was encoded under, so reading it back out of
// that scheme is what leaves the designation itself in hand. A key designated
// this way therefore reaches the same key of the same entity whichever scheme
// the text chose to spell it with.
//
// A line that is not something the scheme in effect writes designates no key
// at all, and saying so is what keeps a text from being read under a scheme it
// was not written under without anything remarking on it.
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
  std::string value;
  // A line that cannot be read out of the scheme in effect designates no key,
  // and the line is consumed either way: the keyword above it said the line is
  // key material, so it is not text of the design whether or not the key came
  // out of it.
  if (!ReadEncodedProtectValue(Trim(line), loc, &value)) return true;
  protect_keywords_.Apply(kKeyPublicKeyKeyword, value);
  CheckKeyBlockDesignation(kKeyPublicKeyKeyword, value, loc);
  return true;
}

// §34.5.13: the keyword announcing the public key a region's data are under
// says that the next line of the file holds that key's encoded value, so the
// line is the designation of a key rather than a line of the design, and it is
// read as the value the keyword was left waiting for.
//
// What the line carries is the key's encoded value rather than the key, and
// §34.5.13 sends the reading to the encoding pragma expression currently in
// effect for the coding scheme it was encoded under, so reading it back out of
// that scheme is what leaves the designation itself in hand. A key designated
// this way therefore reaches the same key of the same entity whichever scheme
// the text chose to spell it with.
//
// Being a designation, it is held to what §34.5.13 requires of one alongside
// the name the region gave its key, exactly as a designation written against a
// keyword is.
//
// A line that is not something the scheme in effect writes designates no key at
// all, and saying so is what keeps a text from being read under a scheme it was
// not written under without anything remarking on it. The line is consumed
// either way: the keyword above it said the line is key material, so it is not
// text of the design whether or not a key came out of it.
//
// Only a line inside a decryption envelope is read this way. §34.5.13 has an
// encrypting tool write this keyword into each protected block the designation
// was used for, with the value beneath it, so an announcement there is one that
// tool produced. Outside every envelope there is no protected block for a
// public key to have been used for, so the text beneath the announcement is
// text of the source like any other and is left to whatever reads it.
bool Preprocessor::TakeDataPublicKeyValue(std::string_view line,
                                          SourceLoc loc) {
  if (!data_public_key_value_next_) return false;
  data_public_key_value_next_ = false;
  std::string value;
  if (!ReadEncodedProtectValue(Trim(line), loc, &value)) return true;
  protect_keywords_.Apply(kDataPublicKeyKeyword, value);
  // §34.5.10.2: the public key just read designates a key of the data_keyowner
  // in effect, so it is held to being unique for that entity like the name
  // beside it. §34.5.13.1 writes it on the line beneath its keyword, which is
  // why the expression-shaped check does not see it.
  CheckDataKeyDesignationValue(kDataPublicKeyKeyword, value, loc);
  CheckDataDesignationAgreement(loc);
  return true;
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

// §34.5.19: the keyword announcing the public key a region's digest is under
// says that the next line of the file holds that key's encoded value, so the
// line is the designation of a key rather than a line of the design, and it is
// read as the value the keyword was left waiting for.
//
// What the line carries is the key's encoded value rather than the key, and
// §34.5.19 sends the reading to the encoding pragma expression currently in
// effect for the coding scheme it was encoded under, so reading it back out of
// that scheme is what leaves the designation itself in hand. A key designated
// this way therefore reaches the same key of the same entity whichever scheme
// the text chose to spell it with.
//
// Being a designation, it is held to what §34.5.19 requires of one alongside
// the name the region gave its digest's key, exactly as a designation written
// against a keyword is.
//
// A line that is not something the scheme in effect writes designates no key at
// all, and saying so is what keeps a text from being read under a scheme it was
// not written under without anything remarking on it. The line is consumed
// either way: the keyword above it said the line is key material, so it is not
// text of the design whether or not a key came out of it.
//
// Only a line inside a decryption envelope is read this way. §34.5.19 has an
// encrypting tool write this keyword into each protected block the designation
// was used for, with the value beneath it, so an announcement there is one
// that tool produced. Outside every envelope there is no protected block for a
// public key to have been used for, so the text beneath the announcement is
// text of the source like any other and is left to whatever reads it.
bool Preprocessor::TakeDigestPublicKeyValue(std::string_view line,
                                            SourceLoc loc) {
  if (!digest_public_key_value_next_) return false;
  digest_public_key_value_next_ = false;
  std::string value;
  if (!ReadEncodedProtectValue(Trim(line), loc, &value)) return true;
  protect_keywords_.Apply(kDigestPublicKeyKeyword, value);
  // §34.5.16.2: the public key just read designates a key of the
  // digest_keyowner in effect, so it is held to being unique for that entity
  // like the name beside it. §34.5.19.1 writes it on the line beneath its
  // keyword, which is why the expression-shaped check does not see it.
  CheckDigestDesignationValue(kDigestPublicKeyKeyword, value, loc);
  CheckDigestDesignationAgreement(loc);
  return true;
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

// §34.5.9 gives a reading of an encoded value three ways to fail, and they are
// different things to be told.
//
// The scheme may be one nothing here provides. Table 34-2 names four
// identifiers and leaves further ones to the implementation, so one outside
// both sets stands for no writing at all: there is nothing to measure the
// characters against, however well formed they are.
//
// Or the scheme may be one this tool has and the value may not be something
// that scheme writes, which says it was written under a different scheme from
// the one standing where it was written. Reporting the two alike would leave an
// author unable to tell an envelope this tool cannot open from one whose
// description of itself does not match what it carries.
//
// Or the characters may be that scheme's writing and stand for a quantity the
// same expression contradicts. Measuring before the value is handed on keeps a
// value of the wrong size from being reported as a key that does not fit.
bool Preprocessor::ReadEncodedProtectValue(std::string_view text, SourceLoc loc,
                                           std::string* bytes) {
  ProtectEncoding encoding = ProtectEncodingInEffect();
  ProtectEncodedValueRead read = ReadProtectEncodedValue(text, encoding, bytes);
  if (read == ProtectEncodedValueRead::kSchemeUnavailable) {
    diag_.Error(loc,
                "protect pragma encoding names an enctype this implementation "
                "does not provide",
                Subclause("34.5.9.2"));
    return false;
  }
  if (read == ProtectEncodedValueRead::kNotWrittenInScheme) {
    diag_.Error(loc,
                "protect pragma value is not written in the encoding in effect",
                Subclause("34.5.9.2"));
    return false;
  }
  if (!ProtectEncodedValueHasStatedSize(encoding, bytes->size())) {
    diag_.Error(loc,
                "protect pragma value stands for a different number of bytes "
                "from the one the encoding in effect states",
                Subclause("34.5.9.2"));
    return false;
  }
  SpendEncodedValueSize();
  return true;
}

// §34.5.9.2 defines the count as the number of bytes in *the* original block of
// data, so it describes the one value written under it rather than the scheme
// the envelope is in. The scheme outlives the value and the count does not:
// left standing, the count an envelope stated for one block would be measured
// against the next value read, and against every value the text recovered out
// of that block goes on to carry -- a designation of a key that a whole block's
// length would never match.
//
// The scheme itself is left exactly as it was written. A text that stated a
// coding scheme once and wrote several values under it stated it for all of
// them, which is why only the count is taken away.
void Preprocessor::SpendEncodedValueSize() {
  ProtectKeywordValue held = protect_keywords_.ValueOf(kEncodingKeyword);
  if (held.defaulted) return;
  ProtectEncoding encoding = ParseProtectEncoding(held.value);
  if (!encoding.has_bytes) return;
  encoding.has_bytes = false;
  protect_keywords_.Apply(kEncodingKeyword, ProtectEncodingValue(encoding));
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
// This is also where a tool that processes SystemVerilog source text meets the
// obligation §34.3 puts on it: the protected regions the text carries are
// decrypted as they are read, so what the step after this one analyses is the
// design rather than the envelope it arrived in.
void Preprocessor::ApplyProtectKeywords(
    const std::vector<PragmaKeywordExpression>& keywords, SourceLoc loc,
    int depth, std::string& output) {
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
    protect_keywords_.Apply(expr.keyword,
                            expr.value.empty() ? expr.value_list : expr.value);
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
    DecryptDataBlock(expr, loc, depth, output);
  }
}

// The key a protected region is read under, which §34.5.10 has selected by
// combining the entity in effect where the region's block is written with what
// that entity's key was designated by: the data_keyowner names the entity that
// provided the keys, and either the data_keyname or the data_public_key picks
// a single one of that entity's keys out.
//
// The two designations are alternatives to one another rather than halves of
// one thing, so a region designating its key by the second is read the same
// way as one designating it by the first, and neither designation is read
// against any entity but the one in effect beside it.
//
// A user who supplied a key under no name at all supplied one key for every
// region, so that key is what a block is read under and the names an envelope
// carries select nothing. That is the whole of what a user with one key needs
// to say, which is why it is not the same thing as a list holding one entry.
// §34.5.25 adds a third designation to those two, and it is the one a region
// carries when what its data are reached through is a key of the region's own
// rather than a key named for the data directly: the name written for the
// region's keys, combined with the entity written beside that name, selects
// the single key the data block of the envelope is opened with. It is consulted
// after the two the data name for themselves, a region naming its data's key
// outright having said what that key is.
std::string_view Preprocessor::ProtectKeyInEffect() const {
  // §34.5.14 settles this ahead of every name a text writes. A key recovered
  // from a key block is the key that opens the data block, not a designation
  // that selects one: it was made for this region alone and travelled inside
  // the envelope, so there is nothing to read it against and nothing a user
  // could have supplied in its place. A region carrying one is therefore opened
  // with it whatever the names beside it would otherwise have reached.
  if (!data_decrypt_key_.empty()) return data_decrypt_key_;
  if (config_.protect_keys.Empty()) return config_.protect_key;
  ProtectKeywordValue owner = protect_keywords_.ValueOf(kDataKeyownerKeyword);
  ProtectKeywordValue name = protect_keywords_.ValueOf(kDataKeynameKeyword);
  std::string_view named = config_.protect_keys.KeyFor(owner.value, name.value);
  if (!named.empty()) return named;
  ProtectKeywordValue public_key =
      protect_keywords_.ValueOf(kDataPublicKeyKeyword);
  std::string_view under_public =
      config_.protect_keys.KeyFor(owner.value, public_key.value);
  if (!under_public.empty()) return under_public;
  return ProtectKeyBlockKey(protect_keywords_, config_.protect_keys);
}

// The key a protected region's digest is read under. §34.5.18 has it selected
// by combining the two names the digest carries -- the entity that provided
// the key, and the name that picks one of that entity's keys out -- and one
// pair reaches one key.
//
// The names the digest carries are its own rather than the ones the data
// carry, so a design whose digest is under a key of one provider and whose
// data are under a key of another is read as it was written. Where the digest
// names no key of its own, what fills its place carries the pairing back to
// the name the data are under, which is the only place §34.5.18 takes it from.
//
// A user who supplied a key under no name at all supplied one key for the
// whole of what a text carries, its digests included: names in the text select
// among keys, and where a user holds one there is nothing to select among. So
// that key stands here for the same reason it stands for a region's block,
// rather than the digest being left with nothing to be read under.
std::string_view Preprocessor::DigestKeyInEffect() const {
  if (config_.protect_keys.Empty()) return config_.protect_key;
  return ProtectDigestKey(protect_keywords_, config_.protect_keys);
}

// §34.5.20 settles this in two steps, and the first outranks every name a text
// writes. A key recovered from a key block is the key that opens the digest,
// not a designation that selects one: it was made for this region alone and
// travelled inside the envelope, so there is nothing to read it against and
// nothing a user could have supplied in its place. Where no block carried one,
// the subclause fills the place from the key the region's data are under, and
// that key reaches here the same way -- as the key itself, recovered from the
// block that carried it.
std::string_view Preprocessor::DigestDecryptKeyInEffect() const {
  if (!digest_decrypt_key_.empty()) return digest_decrypt_key_;
  return data_decrypt_key_;
}

// The designations §34.5.22 names for a digest's key, tried in the order that
// decides them.
//
// A key one of the region's blocks carried comes first, for the reason §34.5.14
// puts a carried key ahead of every name: it is the key rather than something
// selecting one. §34.5.18's pairing of the entity providing the digest's key
// with the name of that key comes next, selecting one of the keys the user
// supplied.
//
// The public key one of that entity's keys is comes after the name rather than
// instead of it. The two are alternative ways of picking one key out of one
// entity's list, so a region writing both has picked out one key twice and the
// order between them decides nothing; a region writing only the second would be
// left designating nothing at all if the name were the only route tried.
//
// A region that wrote none of them has its digest under the key its data are
// under, which is where every default here leads and what a user holding a
// single key supplied for the whole of what a text carries.
std::string_view Preprocessor::DigestBlockKeyInEffect() const {
  std::string_view carried = DigestDecryptKeyInEffect();
  if (!carried.empty()) return carried;
  std::string_view named = DigestKeyInEffect();
  if (!named.empty()) return named;
  std::string_view under_public =
      ProtectDigestKeyByPublicKey(protect_keywords_, config_.protect_keys);
  if (!under_public.empty()) return under_public;
  return ProtectKeyInEffect();
}

// §34.3: envelope decryption recognizes a decryption envelope and puts the
// cleartext of the region it stands for back in its place, for the compilation
// step that follows. The expression carrying that region is the one acted on
// here, and the cleartext is emitted where the envelope was written, so the
// text that leaves the preprocessor is the design.
//
// An expression naming no region, or one written where no decryption envelope
// is open, describes something other than a protected region and is left to
// whatever else reads it. Where a region is named and the user's key is not
// the one it was encrypted under, no cleartext can be put back, and saying so
// is the only way the missing design does not read as an empty one.
//
// What the recovered text is then put through is what §34.3.2 settles. The
// text a region records is source text like any other, so it may hold macro
// usages and it may hold further decryption envelopes -- and each of those is
// read only once the envelope that sealed it has been replaced, because until
// then it is inside a block rather than inside the source. Handing the
// cleartext back to the source loop is what puts it in that order: it is
// substituted for the envelope first, and the loop then reaches its macros and
// its envelopes the same way it reaches those of a file, one step behind the
// replacement that produced them.
//
// §34.5.9 settles the other half of reading such an expression: the block is
// characters and what it records is bytes, so the scheme in effect turns the
// one into the other, and the count that expression carries says how many bytes
// should come out. Both are spent where every encoded value of an envelope is
// read, so a block of the wrong size is turned away there -- before any key is
// offered to it, and so never reported as a key that does not fit.
void Preprocessor::DecryptDataBlock(const PragmaKeywordExpression& expr,
                                    SourceLoc loc, int depth,
                                    std::string& output) {
  // §34.5.15.1 spells the expression as the keyword standing alone, with
  // §34.5.15.2 putting the block on the lines beneath it, and this
  // implementation writes the block as the keyword's own value and reads it
  // back that way. An expression carrying no value therefore names a block this
  // reading cannot reach; what a tool owes an envelope written that way is
  // #3272, and it is not a report against source the standard admits.
  if (expr.keyword != kDataBlockKeyword || expr.value.empty()) return;
  if (!protect_envelopes_.InProtectedRegion()) return;
  std::string block;
  if (!ReadEncodedProtectValue(ProtectPragmaValueBody(expr.value), loc,
                               &block)) {
    return;
  }
  // §34.5.14 has the key a key block carried open the data block that block was
  // written beside, so it is spent here rather than left standing over whatever
  // the text goes on to hold. A key made for one region says nothing about the
  // next, and an envelope that carried none of its own is read under the names
  // it did write rather than under a key some earlier envelope made for itself.
  // Taking a copy is what lets the key be put away before it is used.
  std::string region_key(ProtectKeyInEffect());
  data_decrypt_key_.clear();
  // §34.5.11.2: the data_method states the algorithm the data block is to be
  // decrypted with. This implementation provides one cipher and states its own
  // identifier for it, so a block naming any other algorithm is a block it
  // cannot read -- and reading it under the cipher it does provide would hand
  // back whatever those bytes happen to become rather than the design.
  //
  // A block naming no algorithm is left alone: the keyword has a default and an
  // envelope this tool produced always names its own, so the ones that arrive
  // without a name came from somewhere that took the default with them.
  ProtectKeywordValue method = protect_keywords_.ValueOf(kDataMethodKeyword);
  if (!method.defaulted && !method.value.empty() &&
      method.value != kDataMethod) {
    diag_.Error(loc,
                "protect pragma data block states an encryption algorithm this "
                "implementation does not provide: " +
                    method.value,
                Subclause("34.5.11.2"));
    return;
  }
  std::string cleartext;
  if (!DecryptProtectedBlock(block, region_key, &cleartext)) {
    diag_.Error(loc,
                "protect pragma data block cannot be decrypted with the key "
                "supplied",
                Subclause("34.3.2"));
    return;
  }
  // §34.5.22 owes this block a digest of its own, written immediately after it,
  // so what the block recovered to is held for the digest that follows,
  // together with the key that digest is under. Both are taken before the
  // recovered text is read through, because that text may carry envelopes of
  // its own and each of those spends its keys and checks its digests as it
  // goes; installing this one afterwards is what leaves the outer block's
  // digest checked against the outer block.
  ProtectDigestTarget target{cleartext, std::string(DigestBlockKeyInEffect())};
  // Nothing of the envelope's own is left standing over the recovered text
  // while it is read: a key block of this envelope was the last thing
  // recovered, and a digest_block expression the design itself carries follows
  // no block of the design.
  digest_target_ = ProtectDigestTarget();
  // §34.5.20 has a key a key block carried open the digests of the region that
  // block belongs to, so it is spent here alongside the key that opened the
  // data rather than left standing over whatever the text goes on to hold. The
  // digest still to be checked holds the key it needs already.
  digest_decrypt_key_.clear();
  output.append(ProcessSource(cleartext, loc.file_id, depth));
  digest_target_ = std::move(target);
}

// The identifier is read where the reading stands rather than where the keys
// were supplied, because a text may name one algorithm for one region and
// another for the next: §34.5.21 has the value govern the blocks written after
// it, so what a block's digest belongs to is whatever was in effect beside it.
std::string Preprocessor::DigestMethodInEffect() const {
  return ProtectDigestMethodInEffect(protect_keywords_).value;
}

// The identifier is read where the reading stands rather than where the keys
// were supplied, because a text may name one cipher for one region and another
// for the next: §34.5.17 has the value name what a digest block is opened with,
// so the block a value governs is whichever one stands after it. Where the text
// named none, what stands here is the cipher its data are under, that being the
// default the subclause settles rather than one this implementation chose.
std::string Preprocessor::DigestKeyMethodInEffect() const {
  return ProtectDigestKeyMethodInEffect(protect_keywords_).value;
}

// The identifier is read where the reading stands rather than where the keys
// were supplied, because a text may name one algorithm for one region and
// another for the next: §34.5.24 has the value name what a key block is opened
// with, so the block a value governs is whichever one stands after it.
std::string Preprocessor::KeyMethodInEffect() const {
  return ProtectKeyMethodInEffect(protect_keywords_).value;
}

ProtectEncoding Preprocessor::ProtectEncodingInEffect() const {
  ProtectEncoding encoding =
      ParseProtectEncoding(protect_keywords_.ValueOf(kEncodingKeyword).value);
  // Only the scheme is filled from the default. A length or a count the text
  // did state says something about the blocks it went on to write, whichever
  // scheme it left unsaid.
  if (encoding.enctype.empty()) {
    encoding.enctype = DefaultProtectEncoding().enctype;
  }
  return encoding;
}

}  // namespace delta
