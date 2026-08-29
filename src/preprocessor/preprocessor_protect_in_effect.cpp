// The keys, algorithm identifiers and coding scheme in effect where the
// reading stands.
//
// §34.4 gives the value written against a protect pragma keyword a lexical
// scope: it governs the text after the directive that wrote it rather than the
// envelope, the declaration or the file. What a block is opened with is
// therefore whatever stood beside that block, so each of these reads the
// keywords where the reading has reached rather than where the keys were
// supplied.
//
// §34.5.10, §34.5.12, §34.5.16, §34.5.18 and §34.5.20 pair the entity that
// provided a key with the name, the public key or the carried key that picks
// one of that entity's keys out. §34.5.17, §34.5.21 and §34.5.24 name the
// algorithm a digest block, a digest and a key block are made with. §34.5.9
// names the coding scheme every encoded value of an envelope is written under.
// Each of these selects among the values in effect and reports nothing.

#include <string>
#include <string_view>

#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

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
