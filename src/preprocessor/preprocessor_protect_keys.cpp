#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope.h"
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

// §34.5.9 gives a reading of an encoded value two ways to fail, and they are
// different things to be told.
//
// The scheme may be one nothing here provides. Table 34-2 names four
// identifiers and leaves further ones to the implementation, so an identifier
// outside both sets stands for no writing at all: there is nothing to measure
// the characters against, and a text under it cannot be read however well
// formed it is.
//
// Or the scheme may be one this tool has and the value may not be something
// that scheme writes, which says the value was written under a different
// scheme from the one standing where it was written. Reporting the two alike
// would leave an author unable to tell an envelope this tool cannot open from
// one whose description of itself does not match what it carries.
bool Preprocessor::ReadEncodedProtectValue(std::string_view text, SourceLoc loc,
                                           std::string* bytes) {
  ProtectEncodedValueRead read =
      ReadProtectEncodedValue(text, ProtectEncodingInEffect(), bytes);
  if (read == ProtectEncodedValueRead::kRead) return true;
  if (read == ProtectEncodedValueRead::kSchemeUnavailable) {
    diag_.Error(loc,
                "protect pragma encoding names an enctype this implementation "
                "does not provide");
    return false;
  }
  diag_.Error(loc,
              "protect pragma value is not written in the encoding in effect");
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
    // §34.5.1.1 writes the expression that opens an encryption envelope as the
    // keyword alone, so the same keyword carrying a pragma_value is that
    // expression written in a spelling it is not defined with. Nothing is put
    // in effect for it and no envelope opens: an expression naming a reserved
    // word wrongly says nothing, and saying so is what keeps it from reading
    // as a region the author never meant to leave unprotected.
    if (expr.keyword == kBeginEncryptionKeyword &&
        !OpensEncryptionEnvelope(expr.keyword, expr.has_value)) {
      diag_.Error(loc,
                  "protect pragma begin keyword is written on its own and "
                  "takes no pragma_value");
      continue;
    }
    // Whatever the expression goes on to do to the envelopes, §34.4 has the
    // value it writes against one of the reserved keywords in effect from
    // here on: the scope is the text after this point, not the envelope, the
    // declaration or the file the expression stands in.
    //
    // A keyword whose value is a list of further expressions has that list put
    // in effect for it, the list being what the keyword records. §34.5.9.1
    // defines its keyword that way, and what a later reading needs from it --
    // which coding scheme, how long a line, how many bytes -- is written
    // nowhere else.
    protect_keywords_.Apply(expr.keyword,
                            expr.value.empty() ? expr.value_list : expr.value);
    if (!protect_envelopes_.Apply(expr.keyword, loc)) {
      diag_.Error(loc,
                  "protect pragma nests decryption envelopes more deeply than "
                  "this implementation processes");
      continue;
    }
    CheckDataKeyname(expr, loc);
    CheckDigestKeyname(expr, loc);
    CheckKeyKeyname(expr, loc);
    CheckKeyDesignation(expr, loc);
    ApplyKeyBlockKeywords(expr, loc);
    DecryptDataBlock(expr, loc, depth, output);
  }
}

// §34.5.12: the name written against the data_keyname keyword picks one key
// out of the list of keys known for the entity the data_keyowner keyword names,
// so a name that is not a member of that entity's list picks out nothing and
// is reported.
//
// Which list the name is read against is decided by the value data_keyowner
// has where the name is written, because the same name under another entity is
// another key or none. Reading it against every key the tool holds would let a
// name belonging to one entity stand for a key held by a different one.
//
// A tool holding no keys for that entity holds no list of them either, and a
// name cannot be found missing from a list that was never supplied. There is
// nothing to report about the name then, and it stands.
void Preprocessor::CheckDataKeyname(const PragmaKeywordExpression& expr,
                                    SourceLoc loc) {
  if (expr.keyword != kDataKeynameKeyword || !expr.has_value) return;
  ProtectKeywordValue owner = protect_keywords_.ValueOf(kDataKeyownerKeyword);
  if (!config_.protect_keys.KnowsOwner(owner.value)) return;
  if (config_.protect_keys.KnowsKey(owner.value,
                                    ProtectPragmaValueBody(expr.value))) {
    return;
  }
  diag_.Error(loc,
              "protect pragma data_keyname names no key held by the "
              "data_keyowner in effect");
}

// §34.5.18: the name written against the digest_keyname keyword picks one key
// out of the list of keys known for the entity the digest_keyowner keyword
// names, so a name that is not a member of that entity's list picks out
// nothing and is reported.
//
// The entity the name is read against is the one the digest names, not the one
// the data name. The two may differ -- a design may have its digest under a
// key of one provider and its data under a key of another -- and reading a
// digest key name against the data's provider would let a name belonging to
// one entity's list stand for a key held by a different one.
//
// A tool holding no keys for that entity holds no list of them either, and a
// name cannot be found missing from a list that was never supplied. There is
// nothing to report about the name then, and it stands.
void Preprocessor::CheckDigestKeyname(const PragmaKeywordExpression& expr,
                                      SourceLoc loc) {
  if (expr.keyword != kDigestKeynameKeyword || !expr.has_value) return;
  ProtectKeywordValue owner = protect_keywords_.ValueOf(kDigestKeyownerKeyword);
  if (!config_.protect_keys.KnowsOwner(owner.value)) return;
  if (config_.protect_keys.KnowsKey(owner.value,
                                    ProtectPragmaValueBody(expr.value))) {
    return;
  }
  diag_.Error(loc,
              "protect pragma digest_keyname names no key held by the "
              "digest_keyowner in effect");
}

// §34.5.25: the name written against the key_keyname keyword picks one key out
// of the list of keys known for the entity the key_keyowner keyword names, so
// a name that is not a member of that entity's list picks out nothing and is
// reported.
//
// The entity the name is read against is the one written for the region's own
// keys, not the one written for its data. A region may hold its keys under a
// key of one provider and its data under a key of another, and reading this
// name against the data's provider would let a name belonging to one entity's
// list stand for a key held by a different one.
//
// A tool holding no keys for that entity holds no list of them either, and a
// name cannot be found missing from a list that was never supplied. There is
// nothing to report about the name then, and it stands.
void Preprocessor::CheckKeyKeyname(const PragmaKeywordExpression& expr,
                                   SourceLoc loc) {
  if (expr.keyword != kKeyKeynameKeyword || !expr.has_value) return;
  ProtectKeywordValue owner = protect_keywords_.ValueOf(kKeyKeyownerKeyword);
  if (!config_.protect_keys.KnowsOwner(owner.value)) return;
  if (config_.protect_keys.KnowsKey(owner.value,
                                    ProtectPragmaValueBody(expr.value))) {
    return;
  }
  diag_.Error(loc,
              "protect pragma key_keyname names no key held by the "
              "key_keyowner in effect");
}

// §34.5.10: the values written against data_keyname, data_decrypt_key and
// data_public_key are unique for the entity the data_keyowner keyword names
// where they are written. One value written under a single entity against two
// of those three names would have to designate two of that entity's keys at
// once, so it designates neither, and it is reported.
//
// The entity is what the values are unique for. The same value written under
// two entities is two designations rather than one repeated, because each is
// read against a different list of keys, and it stands.
//
// An expression with nothing written against it designates nothing, and so
// does one whose value is a parenthesized list of further expressions, those
// qualifying a value rather than being one. Neither is a designation this has
// anything to say about.
void Preprocessor::CheckKeyDesignation(const PragmaKeywordExpression& expr,
                                       SourceLoc loc) {
  if (!expr.has_value || expr.value.empty()) return;
  if (!IsProtectKeyDesignationKeyword(expr.keyword)) return;
  ProtectKeywordValue owner = protect_keywords_.ValueOf(kDataKeyownerKeyword);
  std::string_view picked = ProtectPragmaValueBody(expr.value);
  if (protect_key_designations_.Record(owner.value, expr.keyword, picked)) {
    return;
  }
  diag_.Error(loc,
              "protect pragma writes one value against two of the names that "
              "designate a key of the data_keyowner in effect");
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
// §34.5.9 settles the other half of reading such an expression, and it is two
// separate things. The block is characters and what it records is bytes, so
// the coding scheme in effect is what turns the one into the other, and
// without it there is nothing to try a key against. The count the same
// expression carries is of the data before any of that writing was applied, so
// it is measured against the block the reading recovered rather than against
// anything the key went on to produce -- a block that is not the size its
// envelope declares is not that envelope's block whatever key is offered, and
// checking it first is what keeps that from being reported as a key that does
// not fit.
void Preprocessor::DecryptDataBlock(const PragmaKeywordExpression& expr,
                                    SourceLoc loc, int depth,
                                    std::string& output) {
  if (expr.keyword != kDataBlockKeyword || expr.value.empty()) return;
  if (!protect_envelopes_.InProtectedRegion()) return;
  std::string block;
  if (!ReadEncodedProtectValue(ProtectPragmaValueBody(expr.value), loc,
                               &block)) {
    return;
  }
  ProtectEncoding encoding = ProtectEncodingInEffect();
  if (encoding.has_bytes && encoding.bytes != block.size()) {
    diag_.Error(loc,
                "protect pragma data block holds a different number of bytes "
                "from the one the encoding in effect states");
    return;
  }
  std::string cleartext;
  if (!DecryptProtectedBlock(block, ProtectKeyInEffect(), &cleartext)) {
    diag_.Error(loc,
                "protect pragma data block cannot be decrypted with the key "
                "supplied");
    return;
  }
  output.append(ProcessSource(cleartext, loc.file_id, depth));
}

// The identifier is read where the reading stands rather than where the keys
// were supplied, because a text may name one algorithm for one region and
// another for the next: §34.5.21 has the value govern the blocks written after
// it, so what a block's digest belongs to is whatever was in effect beside it.
std::string Preprocessor::DigestMethodInEffect() const {
  return ProtectDigestMethodInEffect(protect_keywords_).value;
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
