#pragma once

#include <cstdint>
#include <span>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

// §34.4 sets aside a fixed set of pragma keyword names for the protect pragma
// and tabulates them; §34.5 is where each of those names is defined. One entry
// of that table: the name, and what the table says the name does.
struct ProtectPragmaKeyword {
  std::string_view name;
  // The account the table gives of the name. It rides beside the name so a
  // name is never listed without what listing it was for.
  std::string_view description;
};

// Every name the table lists, in the order it lists them -- which is also the
// order the definitions behind them are written in. A name that is not here is
// not a pragma keyword of the protect pragma, whichever directive it is
// written on and however it is spelled.
std::span<const ProtectPragmaKeyword> ProtectPragmaKeywords();

// Whether `name` is one of them.
bool IsProtectPragmaKeyword(std::string_view name);

// What the table says `name` does. A name outside the table has no entry, so
// there is nothing to say about it and the result is empty.
std::string_view ProtectPragmaKeywordDescription(std::string_view name);

// A pragma_value spelled as a string carries its quotes. What the keyword
// records is written between them; a value spelled any other way records
// itself.
std::string_view ProtectPragmaValueBody(std::string_view value);

// The tabulated name that carries who wrote the design an envelope holds.
// §34.5.5 has the value written against it identify the IP author by name.
//
// It is tabulated apart from the name carrying uninterpreted documentation so
// that the author can be found without reading a documentation string for one:
// whatever looks for the author looks at this name, rather than parsing what
// some other name happens to carry.
inline constexpr std::string_view kAuthorKeyword = "author";

// The tabulated name that carries whatever further the design's author offered
// about themselves. §34.5.6 has the value written against it hold information
// the IP author supplied beyond the name that identifies them.
//
// It is tabulated apart from the name carrying uninterpreted documentation for
// the reason the author's own name is: whatever looks for what an author said
// about themselves looks at this name, rather than parsing what some other name
// happens to carry. It is a name of its own beside the author's as well, a
// further word about somebody being something other than the name they are
// identified by.
inline constexpr std::string_view kAuthorInfoKeyword = "author_info";

// The tabulated name that carries the name of the tool that performed an
// encryption. §34.5.7 has the value written against it identify that tool by
// name.
//
// The tool doing the encrypting is what generates the expression, and nothing
// an encrypting tool reads settles the value: the only tool the name can stand
// for is the one that wrote the envelope carrying it, so a name found in the
// text being encrypted names some earlier tool rather than this one.
inline constexpr std::string_view kEncryptAgentKeyword = "encrypt_agent";

// The tabulated name that carries whatever further the tool that performed an
// encryption offered about itself. §34.5.8 has the value written against it
// hold information that tool provided beyond the name identifying it.
//
// It is tabulated apart from that name for the reason the author's further
// word is tabulated apart from the author's name: whatever looks for what a
// tool said about itself looks at this name, rather than parsing what some
// other name happens to carry. The two are separate entries of §34.4's table
// rather than one name and a qualifier of it, and the shorter name's
// characters open the longer one, so where one ends and the other begins is
// decided by the spelling.
inline constexpr std::string_view kEncryptAgentInfoKeyword =
    "encrypt_agent_info";

// The tabulated name that carries the name of the key a protected region's
// data are under. §34.5.12.1 writes it with a value against it.
inline constexpr std::string_view kDataKeynameKeyword = "data_keyname";

// The tabulated name that carries who provided that key. A key name is a
// member of one such entity's list of keys and says nothing outside it, so the
// two names are spelled beside one another rather than apart.
inline constexpr std::string_view kDataKeyownerKeyword = "data_keyowner";

// The two remaining tabulated names by which one of that entity's keys is
// picked out: the public key a region's data were put under, and the session
// key for those data. §34.5.10 measures all three against the entity rather
// than against the text as a whole, so they are spelled beside the name of the
// entity they are measured against.
inline constexpr std::string_view kDataPublicKeyKeyword = "data_public_key";
inline constexpr std::string_view kDataDecryptKeyKeyword = "data_decrypt_key";

// Whether `name` is one of the three names that designate a key of a stated
// entity. A name outside those three designates no key, whatever else it may
// do.
bool IsProtectKeyDesignationKeyword(std::string_view name);

// The tabulated name that carries the name of the key a protected region's
// digest is under. §34.5.18.1 writes it with a value against it, and what that
// value names is the key that opens the digest rather than the one that opens
// the data: a design may have its digest under a key of its own.
inline constexpr std::string_view kDigestKeynameKeyword = "digest_keyname";

// The tabulated name that carries who provided that key. §34.5.18 reads a
// digest key name against the list of keys this entity is known to hold and
// pairs the two to reach a single key, so the two names are spelled beside one
// another rather than apart.
inline constexpr std::string_view kDigestKeyownerKeyword = "digest_keyowner";

// The second tabulated name by which one of that entity's keys is picked out:
// the public key the region's digest was put under.
//
// §34.5.19.1 writes it standing alone rather than with a value against it,
// because what it designates is written on the line after it in whatever coding
// scheme is in effect there. It is an alternative to the name given to the
// digest's key rather than a companion of it: §34.5.19 has the two refer to one
// key wherever a text writes both, so a text writing both has picked out one
// key twice.
inline constexpr std::string_view kDigestPublicKeyKeyword = "digest_public_key";

// Whether `name` is one of the three names that designate a key of the entity
// the digest_keyowner names.
//
// §34.5.16 requires the values written against them to be unique for that
// entity, and it names three: the name given to one of that entity's keys, the
// session key for the digest, and the public key one of its keys is. A name
// outside those three designates none of that entity's keys, whatever else it
// may do.
bool IsProtectDigestDesignationKeyword(std::string_view name);

// The tabulated name that carries the name of the key a protected region's own
// keys are under. §34.5.25.1 writes it with a value against it, and what that
// value names is the key that opens the block those keys are held in rather
// than the one that opens the design: a producer may keep the two apart, and a
// reader holding the one has not thereby been given the other.
inline constexpr std::string_view kKeyKeynameKeyword = "key_keyname";

// The tabulated name that carries who provided that key. §34.5.25 reaches a
// single key by combining the two, a key name being a member of one entity's
// list and naming nothing outside it, so the two names are spelled beside one
// another rather than apart.
inline constexpr std::string_view kKeyKeyownerKeyword = "key_keyowner";

// The second tabulated name by which one of that entity's keys is picked out:
// the public key the region's own keys were put under.
//
// §34.5.26.1 writes it standing alone rather than with a value against it,
// because what it designates is written on the line after it in whatever
// encoding is in effect there. It is an alternative to the key name rather
// than a companion of it: §34.5.26 has the two refer to one key wherever a
// text writes both, so a text writing both has picked out one key twice.
inline constexpr std::string_view kKeyPublicKeyKeyword = "key_public_key";

// Whether `name` is one of the two names that designate a key of the entity
// the key_keyowner names.
//
// §34.5.23 puts on that entity the constraints §34.5.10 states for the one
// whose keys the data are under, and what those constraints govern is the
// values written against the names designating a key. These two are the names
// that do so here, and a name outside them designates none of that entity's
// keys, whatever else it may do.
bool IsProtectKeyBlockDesignationKeyword(std::string_view name);

// The value a protect pragma keyword has. `defaulted` marks the value §34.4
// puts in the place of a keyword no directive has written: an envelope missing
// a keyword is described by that keyword's default rather than left
// undescribed, so the absence is something to fill rather than something to
// report.
struct ProtectKeywordValue {
  std::string value;
  bool defaulted;
};

// The protect pragma keyword values a source text has put in effect at the
// point the reading has reached.
//
// The scope tracked here is the lexical one: a value belongs to the position
// in the text where it was written and to everything the reading goes on to
// reach, rather than to the declarative region or the declaration the
// directive happens to stand in. Reading crosses out of a declaration, out of
// a file and on into an included file without any of the values being put
// back, so one of these follows a whole compilation input rather than a file
// or a design element.
class ProtectKeywordScope {
 public:
  // Applies one pragma expression of a protect pragma directive: `keyword`
  // names it, and `value` is the pragma_value written against it, empty where
  // the expression is the keyword standing alone. A name the table does not
  // list is not a protect pragma keyword, so nothing is put in effect for it.
  void Apply(std::string_view keyword, std::string_view value);

  // The value in effect for `keyword`, which is its default until a directive
  // writes one.
  ProtectKeywordValue ValueOf(std::string_view keyword) const;

  // The name of the key a digest is under at the point the reading has
  // reached.
  //
  // §34.5.18 settles what stands there when no digest_keyname has been
  // specified: the name in effect for the key the data are under. A design
  // whose digest is under the same key as its data says so by saying nothing,
  // so the absence is filled from the other name rather than leaving the
  // digest with no key named for it at all. A digest_keyname a directive did
  // specify stands on its own, and whatever data_keyname goes on to say leaves
  // it as it is.
  //
  // A value reached by that filling is reported as defaulted, because a
  // default rule is what put it there rather than a directive naming a key for
  // the digest.
  ProtectKeywordValue DigestKeynameInEffect() const;

  // The name of the entity that provided the key a digest is under at the
  // point the reading has reached.
  //
  // §34.5.16 settles what stands there when no digest_keyowner has been
  // specified: the value data_keyowner has where the reading stands. A design
  // whose digest key came from the provider its data key came from says so by
  // saying nothing, so the absence is filled from the other name rather than
  // leaving the digest's key with no provider named for it at all. A
  // digest_keyowner a directive did specify stands on its own, and whatever
  // data_keyowner goes on to say leaves it as it is.
  //
  // A value reached by that filling is reported as defaulted, because a
  // default rule is what put it there rather than a directive naming a
  // provider for the digest's key.
  ProtectKeywordValue DigestKeyownerInEffect() const;

  // The public key that one of that entity's keys is at the point the reading
  // has reached, which is the other designation the digest's key is picked out
  // by.
  //
  // §34.5.19 settles what stands there when no digest_public_key has been
  // specified: the value in effect for the public key the region's data are
  // under. A design whose digest is under the public key its data are under
  // says so by saying nothing, so the absence is filled from that designation
  // rather than leaving the digest with no public key designated for it at all.
  // A digest_public_key a directive did specify stands on its own, and whatever
  // data_public_key goes on to say leaves it as it is.
  //
  // A value reached by that filling is reported as defaulted, because a default
  // rule is what put it there rather than a directive designating a key for the
  // digest.
  ProtectKeywordValue DigestPublicKeyInEffect() const;

 private:
  struct Entry {
    std::string keyword;
    std::string value;
  };
  // One entry per keyword a directive has written, in first-written order. A
  // keyword written again keeps its entry and takes the newer value, because
  // what is in effect is the most recent writing of it.
  std::vector<Entry> in_effect_;
};

// One key a tool holds, identified the way §34.5.12 identifies a key: by the
// entity whose list it belongs to, and by the name that picks it out of that
// list.
//
// Neither half identifies a key on its own. A name is a member of one entity's
// list, and the same name written under another entity is another key or no
// key at all, which is why the two travel together with the material they
// select rather than the name travelling alone.
//
// The designating half is whichever of the names the standard admits for it
// was written: §34.5.10 lets a key be picked out by the name given to it or by
// the public key its data were put under, and the two are alternatives, so
// what is held here is the designation rather than one particular spelling
// of it.
struct ProtectKey {
  std::string owner;
  std::string name;
  std::string key;
};

// The keys a tool knows, held as the lists §34.5.12 reads a name against: one
// list per entity that provided keys, and a name outside the list of the
// entity it was written under naming nothing.
//
// A tool that was given no keys for an entity holds no list for it. That is a
// different state from a list the name is missing from: there is nothing for
// the name to be absent from, so nothing about the name can be concluded
// either way.
class ProtectKeyList {
 public:
  void Add(ProtectKey key);

  // Whether any key at all is known for `owner`, which is whether there is a
  // list of that entity's keys to read a name against.
  bool KnowsOwner(std::string_view owner) const;

  // Whether `name` is a member of the list of keys known for `owner`.
  bool KnowsKey(std::string_view owner, std::string_view name) const;

  // The single key that `owner` and `name` together select, and an empty view
  // where the two select none.
  std::string_view KeyFor(std::string_view owner, std::string_view name) const;

  // Whether the tool was given any keys under a name at all.
  bool Empty() const { return keys_.empty(); }

 private:
  const ProtectKey* Find(std::string_view owner, std::string_view name) const;

  std::vector<ProtectKey> keys_;
};

// The designations a source text has written for the keys of the entities it
// names.
//
// §34.5.10 requires the three designating names to carry values that are
// unique for the entity they are written under. The entity is what they are
// unique for, so one value written under two entities is two designations
// rather than one repeated: each is read against a different list of keys.
// Written under a single entity against two of the three names, one value
// would have to pick out two of that entity's keys at once, and that is the
// repetition the requirement rules out.
class ProtectKeyDesignations {
 public:
  // Records `value` as written against `keyword` for the entity `owner`, and
  // returns whether the value is still unique for that entity. The designation
  // is recorded either way, because a value written a third time is as much a
  // repetition as it was the second time.
  bool Record(std::string_view owner, std::string_view keyword,
              std::string_view value);

 private:
  struct Designation {
    std::string owner;
    std::string keyword;
    std::string value;
  };
  std::vector<Designation> written_;
};

// The single key that opens a protected region's digest: the one that the
// entity named by the digest_keyowner in effect and the digest key name in
// effect select together out of `keys`.
//
// Neither name reaches a key on its own, a key name being a member of one
// entity's list and meaning nothing outside it, which is why §34.5.18 has the
// two combined -- by the tool that encrypts a digest to find what to encrypt
// it under, and by the tool that decrypts one to find what to open it with.
// One pair reaches one key, so the same combining serves both.
//
// The result is empty where the pair reaches none of the keys held, which is
// what a tool that was given no key for that entity and name sees.
std::string_view ProtectDigestKey(const ProtectKeywordScope& scope,
                                  const ProtectKeyList& keys);

// The single key that opens the keys a protected region is held under: the one
// that the entity named by the key_keyowner in effect and the designation in
// effect for one of that entity's keys select together out of `keys`.
//
// Neither half reaches a key on its own, a designation being a member of one
// entity's list and meaning nothing outside it, which is why §34.5.25 has the
// two combined -- by the tool that encrypts a region's keys to find what to
// encrypt them under, and by the tool that reads the region to find the key
// its data are reached through. One pair reaches one key, so the same
// combining serves both.
//
// §34.5.23 states which designations the entity may be combined with, and
// there are two: the name given to one of its keys, and the public key one of
// them is. They are alternatives to one another, so a text writing only the
// second is read the same way as one writing only the first, and the name is
// tried first because a text writing both has said the same thing twice.
//
// The result is empty where the pair reaches none of the keys held, which is
// what a tool that was given no key for that entity and designation sees.
std::string_view ProtectKeyBlockKey(const ProtectKeywordScope& scope,
                                    const ProtectKeyList& keys);

// What is known about whether the two designations in effect for a key of the
// entity the key_keyowner names pick out one key or two.
//
// The question is only decided where the tool holds a key under each of them.
// With one designation reaching nothing there is no second key for the first
// to disagree with, and a tool that was given no keys at all has nothing to
// compare, so in both cases what the text wrote is left as it stands.
enum class ProtectKeyAgreement : uint8_t {
  kUndecided,
  kSameKey,
  kDifferentKeys
};

// Which of those three the key_keyname and key_public_key in effect are in.
//
// §34.5.26 has the two refer to the same key wherever a text writes both. A
// name and a public key are two ways of picking one key out of one entity's
// list rather than two keys to hold at once, so a text whose two designations
// reach different keys has asked for a key the region cannot be under.
ProtectKeyAgreement ProtectKeyBlockDesignationsAgree(
    const ProtectKeywordScope& scope, const ProtectKeyList& keys);

// The same question, asked of the two designations in effect for a key of the
// entity the data_keyowner names: the name given to that key, and the public
// key it is.
//
// §34.5.13 has the two refer to the same key wherever a text writes both. They
// are two ways of picking one key out of one entity's list rather than two keys
// to hold at once, so a text whose two designations reach different keys has
// asked for its data to be under a key they cannot both be.
//
// It is only decided where the tool holds a key under each of them, for the
// reason it is only decided there for the region's own keys: with one
// designation reaching nothing there is no second key for the first to disagree
// with, and a tool that was given no keys at all has nothing to compare.
ProtectKeyAgreement ProtectDataDesignationsAgree(
    const ProtectKeywordScope& scope, const ProtectKeyList& keys);

// The same question again, asked of the two designations a text wrote for a key
// of the entity the digest_keyowner names: the name given to that key, and the
// public key it is.
//
// §34.5.19 has the two refer to the same key wherever a text writes both. They
// are two ways of picking one key out of one entity's list rather than two keys
// to hold at once, so a text whose two designations reach different keys has
// asked for a key its digest cannot be under.
//
// The question is asked of the designations a text really wrote rather than of
// the values standing in their places, because it is written of a text that
// wrote both. Where one of them was left out, what fills its place comes from
// the region's data, and the two designations written there answer to their own
// subclause rather than being compared a second time here.
//
// It is only decided where the tool holds a key under each of them, for the
// reason it is only decided there for the region's data: with one designation
// reaching nothing there is no second key for the first to disagree with, and a
// tool that was given no keys at all has nothing to compare.
ProtectKeyAgreement ProtectDigestDesignationsAgree(
    const ProtectKeywordScope& scope, const ProtectKeyList& keys);

// The keyword written as a directive carrying `author`, for naming inside a
// protected envelope whoever wrote the design that envelope holds.
//
// §34.5.5 has the expression placed in a directive the protected envelope
// encloses and kept out of the data block, so what an envelope says about its
// author is readable without a key. An expression swept into the block would
// put the author's name behind the very door the author closed.
//
// `author` is the pragma_value as the source wrote it, quotes and all where it
// had them, and it goes back the same way. What is placed in the directive is
// the expression the source wrote, so a name written bare that came back in
// quotes would be a different pragma_value from the one placed there.
std::string ProtectAuthorDirective(std::string_view author);

// The keyword written as a directive carrying `author_info`, for stating inside
// a protected envelope whatever further the design's author offered about
// themselves.
//
// §34.5.6 has the expression placed in a directive the protected envelope
// encloses and kept out of the data block, so what an envelope carries of its
// author's own further word is readable without a key. An expression swept into
// the block would put that word behind the very door the author closed.
//
// `author_info` is the pragma_value as the source wrote it, quotes and all
// where it had them, and it goes back the same way. What is placed in the
// directive is the expression the source wrote, so a value written bare that
// came back in quotes would be a different pragma_value from the one placed
// there.
std::string ProtectAuthorInfoDirective(std::string_view author_info);

// The keyword written as a directive carrying `keyname`, for stating in the
// clear which key a protected region's data are under. §34.5.12 has the name
// output as cleartext, and encrypting it into the very block it names the key
// for would leave a reader nothing to open that block with.
std::string ProtectDataKeynameDirective(std::string_view keyname);

// The keyword written as a directive carrying `keyname`, for stating in the
// clear which key a protected region's digest is under.
//
// §34.5.18 has that name output as cleartext, the one exception being a
// digital envelope, where it travels inside the key block encrypted under the
// key method and the key that method names. This implementation offers no
// digital envelope, so the exception never arises and the name is always
// written as it stands. A name swept into the encrypted block would leave a
// reader unable to learn what opens the digest without opening the block
// first.
std::string ProtectDigestKeynameDirective(std::string_view keyname);

// The keyword written as a directive carrying `keyname`, for stating in the
// clear which key a protected region's own keys are under.
//
// §34.5.25 has that name written as cleartext in what an encrypting tool puts
// out, and it is the region's keys that the name reaches. A name swept into
// the encrypted block instead would have to be read out of the very block it
// is needed to open, so a reader would be left with no way in at all.
std::string ProtectKeyKeynameDirective(std::string_view keyname);

// The keyword written as a directive carrying `keyowner`, for stating in the
// clear whose keys a protected region's data are under.
//
// §34.5.10 has the entity's name unchanged in what an encrypting tool writes
// out, the one exception being a digital signature, where it goes into a key
// block under the key method instead. This implementation offers no digital
// envelope, so the exception never arises and the name is always written as it
// stands. A name swept into the block it identifies the keys for would leave a
// reader unable to learn whose key opens that block without first opening it.
std::string ProtectDataKeyownerDirective(std::string_view keyowner);

// The keyword written as a directive carrying `keyowner`, for stating in the
// clear whose keys a protected region's digest is under.
//
// §34.5.16 has the entity's name unchanged in the output file, the one
// exception being a digital signature, where it is encrypted under the cipher
// named for the digest's key and placed in a block holding that key. This
// implementation writes no such block, so the exception never arises and the
// name is always written as it stands. A name swept inside an encrypted block
// would leave a reader unable to learn whose key opens the digest without
// first opening the very thing that digest is there to vouch for.
//
// `keyowner` is the pragma_value as the source wrote it, quotes and all where
// it had them, and it is written back the same way. Unchanged is meant of the
// value: a name written as a bare identifier and returned in quotes has been
// changed, whatever it still denotes.
std::string ProtectDigestKeyownerDirective(std::string_view keyowner);

// The keyword written as a directive carrying `keyowner`, for stating in the
// clear whose keys a protected region's own keys are under.
//
// §34.5.23 has the entity's name unchanged in what an encrypting tool writes
// out, and states no exception to that: where the name of the entity whose key
// the data are under travels inside a key block when a digital signature is
// used, this one has nowhere to travel to, being the name of the entity whose
// key opens that very block. A name swept into the block would have to be read
// out of the block it is needed to open, so a reader would be left with no way
// in at all.
//
// `keyowner` is the pragma_value as the source wrote it, quotes and all where
// it had them, and it is written back the same way. Unchanged is meant of the
// value: a name written as a bare identifier and returned in quotes has been
// changed, whatever it still denotes.
std::string ProtectKeyKeyownerDirective(std::string_view keyowner);

// The keyword written as a directive carrying `method`, for stating in the
// clear which algorithm the digests of a protected region are computed with.
//
// §34.5.21 has that identifier unchanged in what an encrypting tool writes
// out, the one exception being a digital signature, where it travels inside a
// key block under the key method. This implementation offers no digital
// envelope, so the exception never arises and the identifier is always written
// as it stands. An identifier swept into the encrypted block would leave a
// reader unable to learn how a digest is recomputed without first opening the
// very block that digest is there to vouch for.
//
// `method` is the pragma_value as the source wrote it, quotes and all where it
// had them, and it is written back the same way. Unchanged is meant of the
// value: an identifier written bare and returned in quotes has been changed,
// whatever it still names.
std::string ProtectDigestMethodDirective(std::string_view method);

// The keyword written as a directive carrying `method`, for stating in the
// clear which algorithm the keys of a protected region are encrypted under.
//
// §34.5.24 has that identifier unchanged in the output file and states no
// exception at all: the exception the identifier naming the cipher for the data
// has is a key block, and this is the identifier naming the cipher that opens
// that very block. One swept inside would have to be read out of the block it
// is needed to open, so a reader would be left with no way in at all.
//
// `method` is the pragma_value as the source wrote it, quotes and all where it
// had them, and it is written back the same way. Unchanged is meant of the
// value: an identifier written bare and returned in quotes has been changed,
// whatever it still names.
std::string ProtectKeyMethodDirective(std::string_view method);

// The keyword written as a directive designating, by the public key it is,
// which of that entity's keys a protected region's own keys are under.
//
// §34.5.26 writes the designation on the line after the keyword rather than
// against it, so what this produces is two lines: the keyword standing alone
// and `encoded_key` beneath it.
//
// `encoded_key` is the key already written in the coding scheme the envelope
// carrying it declares, which is what §34.5.9 has such a value spelled with,
// and it is the whole of that line. It is not a pragma_value and is not read
// as one, so a key is carried across whichever characters that scheme happened
// to spell it with.
std::string ProtectKeyPublicKeyDirective(std::string_view encoded_key);

// The keyword written as a directive designating, by the public key it is,
// which of that entity's keys a protected region's data are under.
//
// §34.5.13.1 writes the keyword standing alone rather than with a value against
// it, because what it designates is written on the line after it, so what this
// produces is two lines: the keyword and `encoded_key` beneath it.
//
// §34.5.13 has the keyword written into every protected block the designation
// was used for, followed by that value, and states no exception at all: a
// region picked out its key this way and a reader of the block has to pick out
// the same key, so a designation left among the lines that stop being readable
// would name the key from behind the door it opens.
//
// `encoded_key` is the key already written in the coding scheme the envelope
// carrying it declares, which is what §34.5.13 has that value spelled with, and
// it is the whole of that line. It is not a pragma_value and is not read as
// one, so a key is carried across whichever characters that scheme happened to
// spell it with.
std::string ProtectDataPublicKeyDirective(std::string_view encoded_key);

// The keyword written as a directive designating, by the public key it is,
// which of that entity's keys a protected region's digest is under.
//
// §34.5.19.1 writes the keyword standing alone rather than with a value against
// it, because what it designates is written on the line after it, so what this
// produces is two lines: the keyword and `encoded_key` beneath it.
//
// §34.5.19 has the keyword written into every protected block the designation
// was used for, followed by that value, and states no exception at all: a
// region picked its digest's key out this way and a reader of that digest has
// to pick out the same key, so a designation left among the lines that stop
// being readable would name the key from behind the very block the digest is
// there to vouch for.
//
// `encoded_key` is the key already written in the coding scheme the envelope
// carrying it declares, which is what §34.5.19 has that value spelled with, and
// it is the whole of that line. It is not a pragma_value and is not read as
// one, so a key is carried across whichever characters that scheme happened to
// spell it with.
std::string ProtectDigestPublicKeyDirective(std::string_view encoded_key);

// What a tool writes into an envelope of its own making to say how that
// envelope was made.
//
// §34.4 asks a tool that produces envelopes to state every keyword bearing on
// each one, and the reason is the lexical scope the same subclause gives those
// keywords. A keyword an envelope leaves unwritten is filled from whatever the
// reading had in effect on arriving there, which is a different value
// depending on what the envelope was placed beside and which file it was read
// after. An envelope stating its own is read the same way wherever it ends up.
//
// The four named here are the ones that bear on an envelope this
// implementation writes: who made it, what that maker offers further about
// itself, what its data are under, and how its encoded blocks are spelled.
// Their values are the tool's own, because the standard settles neither what a
// tool has to say about itself, nor the cipher it encrypts with, nor the scheme
// it writes the encrypted block in.
//
// `encoding` is the whole pragma_value of that keyword rather than the name of
// a scheme, because §34.5.9.1 spells the value as a list of subkeywords and
// the scheme is only the first of them.
struct ProtectEnvelopeDescription {
  std::string_view encrypt_agent;
  // Whatever further the tool offers about itself, empty where it offers
  // nothing. §34.5.8 asks for that expression only where a tool provided a
  // value, so an empty one is a tool with nothing further to say rather than a
  // value to be written out empty: an envelope carrying the keyword with an
  // empty string against it would offer a reader nothing while stating that it
  // offers something.
  std::string_view encrypt_agent_info;
  std::string_view data_method;
  std::string_view encoding;
};

// Those keywords as directives, one per line, for writing inside an envelope a
// tool has just produced.
std::string ProtectEnvelopeDescriptionDirectives(
    const ProtectEnvelopeDescription& description);

// The directive that puts the protect pragma keywords back to their default
// values. §34.4 recommends one after each envelope, so that what an envelope
// stated about itself is not left standing over whatever comes after it.
std::string ProtectKeywordResetDirective();

}  // namespace delta
