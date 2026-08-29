#pragma once

#include <cstddef>
#include <string>
#include <string_view>

#include "helpers_protect_keys.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

// The §34.5.3 texts a test writes: an encryption region, a model somebody
// sealed already, and the values both are spelled out of. They are shared
// because §34.5.3.2's description is covered in two files and five of its six
// sections reach the same texts.
// test/src/unit/test_preprocessor_subclause_34_05_03_02a.cpp covers the three
// ENCRYPTION INPUT headings, and
// test/src/unit/test_preprocessor_subclause_34_05_03_02b.cpp covers ENCRYPTION
// OUTPUT and the two DECRYPTION INPUT headings.
//
// The constants name the two entities and the keys each provided, the
// statements the two designs enclose, and the ciphers each model states for its
// own blocks. The functions write the texts out of them: Design and the
// SealedModel functions write a design and a model an earlier encryption
// sealed, the Region functions enclose one in an encryption region,
// EncryptedUnderNames and EncryptedUnderThePublicKey drive a text through the
// encrypting half, and Without takes one expression back out of an envelope
// that was produced.
//
// A text only one of the six sections reaches is written beside that section's
// cases rather than here.

// The entity writing the larger model, and the name picking its key out of the
// list of keys that entity provided. §34.5.10 and §34.5.12 give the pair, and
// neither half reaches a key alone.
inline constexpr std::string_view kAuthorEntity = "Acme Corp";
inline constexpr std::string_view kAuthorKeyName = "design-2026";
inline constexpr std::string_view kAuthorKey = "acme-design-key";

// §34.5.10 lets one of that entity's keys be picked out by the public key it is
// rather than by the name given to it, and §34.5.13 has that value written on
// the line beneath the keyword announcing it. This is the value; the key it
// selects is the same one the name above selects, the two being alternative
// ways into one list rather than two keys.
inline constexpr std::string_view kAuthorPublicKey = "acme-public-key";

// The same pair for whoever sealed the model being resealed. Their key is
// supplied to the tool alongside the one above, so a run that let their names
// displace the current ones would reach a real key and produce a real envelope
// -- one nothing holding the current author's key could open.
inline constexpr std::string_view kSealerEntity = "Other Corp";
inline constexpr std::string_view kSealerKeyName = "other-2019";
inline constexpr std::string_view kSealerKey = "other-legacy-key";

// The statement the larger model encloses, and the one the sealed model that
// was produced by an earlier run of the encrypting half encloses. Neither
// survives the writing of a block, so finding either in a tool's output is
// finding text that was not sealed.
inline constexpr std::string_view kOuterStatement = "initial result = 42;";
inline constexpr std::string_view kInnerStatement = "initial sealed = 7;";

// A value written inside the sealed model that nothing else in any text below
// spells. It is long enough that finding it in an output is finding it carried
// rather than coincided with.
inline constexpr std::string_view kSealedBlockMarker = "SEALEDMODELBLOCKMARKER";

// The identifier the sealed model names for the cipher its own block is under.
// §34.5.11 defines the keyword; what it is doing here is standing as a value
// the current encryption would be writing out if it had read the sealed model's
// description as its own.
inline constexpr std::string_view kSealerMethod = "x-legacy-cipher";

// The identifier this implementation states for the blocks it writes, which is
// the method the current encryption is running under.
inline constexpr std::string_view kCurrentMethod = "x-deltahdl-stream";

// Both entities' keys, supplied to whichever half is running. Holding the
// sealed model's key too is what makes a case reaching this list
// discriminating: a run that read the sealed model's names as its own would
// find a key under them rather than falling back to the current author's for
// want of one.
inline ProtectKeyList BothEntitiesKeys() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kAuthorEntity, kAuthorKeyName, kAuthorKey));
  keys.Add(KeyOf(kSealerEntity, kSealerKeyName, kSealerKey));
  return keys;
}

// One key of the current author's, held under the public key it is rather than
// under a name given to it.
//
// It is a list of its own rather than an entry added to the one above, because
// the two lists are asked different questions. A region designating its key by
// public key alone reaches this list only through that designation, so a run
// that never made the designation is left with no key -- which is what makes
// the two placements of the designation tell apart. A list that also held the
// key under a name would answer either way.
inline ProtectKeyList KeysUnderThePublicKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kAuthorEntity, kAuthorPublicKey, kAuthorKey));
  return keys;
}

// The same, under the keys the two entities provided, which is what a region
// naming an entity and one of its keys is encrypted with.
inline std::string EncryptedUnderNames(const std::string& src) {
  return EncryptEnvelopes(src, {}, BothEntitiesKeys());
}

// The same again, under the one key held by the public key it is.
inline std::string EncryptedUnderThePublicKey(const std::string& src) {
  return EncryptEnvelopes(src, {}, KeysUnderThePublicKey());
}

// The design an author seals, written as the region §34.5.1.1 and §34.5.2.1
// delimit, enclosing `statement`.
inline std::string Design(std::string_view statement) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(statement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

// A model somebody sealed earlier, written by hand as the decryption envelope
// §34.5.3.1 opens and §34.5.4.1 closes.
//
// What it describes itself with is the real syntax of the dependencies this
// rule consumes: §34.5.5's author, §34.5.11's identifier for the cipher its
// block is under, §34.5.10's entity and §34.5.12's key name, and §34.5.15's
// block itself. Every one of them is a value the current encryption would be
// writing out if the block's contents were read as description rather than as
// cleartext, which is what makes their absence from a produced envelope worth
// asserting.
inline std::string SealedModel() {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect author=\"").append(kSealerEntity).append("\"\n");
  text.append("`pragma protect data_method=\"").append(kSealerMethod);
  text.append("\"\n");
  text.append("`pragma protect data_keyowner=\"").append(kSealerEntity);
  text.append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(kSealerKeyName);
  text.append("\"\n");
  text.append("`pragma protect data_block=\"").append(kSealedBlockMarker);
  text.append("\"\n");
  text.append("`pragma protect end_protected\n");
  return text;
}

// A sealed model that describes itself with names only.
//
// A block of its own would be tried against the reader's key wherever this
// model is met -- standing outside every region, or recovered out of the block
// of one -- and reported for not opening, which would say nothing about the
// names. What is under test in either position is which text the names reach,
// so the names are all there is.
inline std::string SealedModelNamingItsOwnKeys() {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect author=\"").append(kSealerEntity).append("\"\n");
  text.append("`pragma protect data_keyowner=\"").append(kSealerEntity);
  text.append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(kSealerKeyName);
  text.append("\"\n");
  text.append("`pragma protect end_protected\n");
  return text;
}

// §34.5.13's designation of the key a region's data are under, in the spelling
// that subclause defines: the keyword standing alone, with the key's encoded
// value written on the line beneath it rather than against the keyword.
//
// This is a second shape a sealed model's contents can take. The keywords
// tested above carry what they say on their own line; this one says something
// about the line after it, so a reading that failed to pass over it would take
// a line of somebody else's model for the key its own data are to be under.
inline std::string PublicKeyDesignation() {
  std::string text = "`pragma protect data_public_key\n";
  text.append(kAuthorPublicKey).append("\n");
  return text;
}

// An encryption region enclosing `sealed`, describing itself with the names of
// the entity running the encryption now.
//
// The names stand ahead of the sealed model on purpose. They are the values in
// effect where that model is reached, so they are exactly what the subclause
// forbids the model's own contents from displacing, and the envelope this
// region becomes states them in the clear where a test can read them off.
inline std::string NamedRegionAround(std::string_view sealed) {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect author=\"").append(kAuthorEntity).append("\"\n");
  text.append("`pragma protect data_keyowner=\"").append(kAuthorEntity);
  text.append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(kAuthorKeyName);
  text.append("\"\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(sealed);
  text.append("`pragma protect end\n");
  return text;
}

// An encryption region enclosing `sealed` and naming nobody, for the tests that
// run both halves under the single exchange key.
inline std::string UnnamedRegionAround(std::string_view sealed) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(sealed);
  text.append("`pragma protect end\n");
  return text;
}

// A region whose one designation of a key is §34.5.13's, with `designation`
// standing where that designation is to be read from.
//
// The region states §34.5.9's identity scheme for itself, which is what lets
// the key's value be written as itself on the line the keyword speaks for. It
// names no key by name at all, so the public key is the region's only route to
// one: a run that never reached the designation is left with nothing to encrypt
// the region under, and the region goes back readable.
inline std::string RegionDesignatingItsKeyByPublicKey(
    std::string_view designation) {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect data_keyowner=\"").append(kAuthorEntity);
  text.append("\"\n");
  text.append("`pragma protect encoding=(enctype=\"raw\")\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(designation);
  text.append("`pragma protect end\n");
  return text;
}

// `written` with the first line spelling `line` removed.
//
// A decryption envelope cannot be written out by hand -- what its block holds
// depends on the key the region was sealed under -- so an envelope missing one
// of its expressions is made by taking that expression out of a real produced
// one. A text the line was never found in comes back as it stands, and the
// expectations of whichever test asked for the removal then fail on the
// envelope that was never altered.
inline std::string Without(const std::string& written,
                           const std::string& line) {
  size_t at = written.find(line);
  if (at == std::string::npos) return written;
  std::string shortened(written);
  shortened.erase(at, line.size());
  return shortened;
}
