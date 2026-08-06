// The reading that holds a protected region's key designations to the entity
// they were written under.
//
// §34.5.12, §34.5.18 and §34.5.25 each have a name written against a keyword
// pick one key out of the list of keys held for the entity in effect beside it,
// and §34.5.10 and §34.5.16 each have the values designating one entity's key
// be unique among themselves. Both kinds of rule turn on which entity is in
// effect where the value was written rather than on the value alone, so they
// are read together and apart from the machinery that goes on to open a block
// with what they settled.

#include <string_view>

#include "common/diagnostic.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

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
              "data_keyowner in effect",
              Subclause("34.5.12"));
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
// Where the digest named no entity of its own, §34.5.16 is what puts one there:
// a text silent about whose key its digest is under is read under the entity
// whose key its data are under. The name is then held against that entity's
// list, which is the list the text really reached for.
//
// A tool holding no keys for that entity holds no list of them either, and a
// name cannot be found missing from a list that was never supplied. There is
// nothing to report about the name then, and it stands.
void Preprocessor::CheckDigestKeyname(const PragmaKeywordExpression& expr,
                                      SourceLoc loc) {
  if (expr.keyword != kDigestKeynameKeyword || !expr.has_value) return;
  ProtectKeywordValue owner = protect_keywords_.DigestKeyownerInEffect();
  if (!config_.protect_keys.KnowsOwner(owner.value)) return;
  if (config_.protect_keys.KnowsKey(owner.value,
                                    ProtectPragmaValueBody(expr.value))) {
    return;
  }
  diag_.Error(loc,
              "protect pragma digest_keyname names no key held by the "
              "digest_keyowner in effect",
              Subclause("34.5.18"));
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
              "key_keyowner in effect",
              Subclause("34.5.25"));
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
  if (!protect_key_designations_.Record(owner.value, expr.keyword, picked)) {
    diag_.Error(loc,
                "protect pragma writes one value against two of the names that "
                "designate a key of the data_keyowner in effect",
                Subclause("34.5.10"));
  }
  // §34.5.13 asks something further of the two designations that are still
  // unique for the entity: a name given to one of its keys and a public key one
  // of them is refer to the same key wherever a region wrote both. The name
  // just written may be the second half of such a pair, so the pair is looked
  // at from here as well as from the line a public key arrives on.
  CheckDataDesignationAgreement(loc);
}

// §34.5.16: the values written against digest_keyname, digest_decrypt_key and
// digest_public_key are unique for the entity that provided the key the digest
// is under, where they are written. One value written under a single entity
// against two of those three names would have to designate two of that entity's
// keys at once, so it designates neither, and it is reported.
//
// The entity is what the values are unique for. The same value written under
// two entities is two designations rather than one repeated, because each is
// read against a different list of keys, and it stands.
//
// Which entity that is comes from the same subclause: a text naming none for
// its digest is read under the one whose key its data are under, so a text
// silent about the digest's provider has still specified one and its
// designations are unique for that one. That is also why these are recorded
// apart from the designations written for the entity the data name directly:
// the two entities may be the same and may differ, and a value serving a
// digest's provider has repeated nothing said about a data provider that
// happens to be another party.
//
// An expression with nothing written against it designates nothing, and so
// does one whose value is a parenthesized list of further expressions, those
// qualifying a value rather than being one. Neither is a designation this has
// anything to say about.
void Preprocessor::CheckDigestDesignation(const PragmaKeywordExpression& expr,
                                          SourceLoc loc) {
  if (!expr.has_value || expr.value.empty()) return;
  if (!IsProtectDigestDesignationKeyword(expr.keyword)) return;
  ProtectKeywordValue owner = protect_keywords_.DigestKeyownerInEffect();
  std::string_view picked = ProtectPragmaValueBody(expr.value);
  if (!protect_digest_designations_.Record(owner.value, expr.keyword, picked)) {
    diag_.Error(loc,
                "protect pragma writes one value against two of the names that "
                "designate a key of the digest_keyowner in effect",
                Subclause("34.5.16"));
  }
  // §34.5.19 asks something further of the two designations that are still
  // unique for the entity: a name given to one of its keys and a public key
  // one of them is refer to the same key wherever a region wrote both. The
  // name just written may be the second half of such a pair, so the pair is
  // looked at from here as well as from the line a public key arrives on.
  CheckDigestDesignationAgreement(loc);
}

}  // namespace delta
