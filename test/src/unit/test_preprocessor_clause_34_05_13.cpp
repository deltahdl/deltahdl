// §34.5.13 data_public_key.
//
// The subclause defines one of the protect pragma keywords §34.4 tabulates,
// and says five things about it.
//
//   Its expression is written standing alone, with nothing against it.
//
//   Written in an encrypting tool's input, it says the line after it holds the
//   encoded value of the public key the data are to be encrypted under. The
//   line is that value rather than text of the design.
//
//   How those characters are read is settled by the encoding pragma expression
//   currently in effect, so one key spelled under two coding schemes is one
//   designation written twice rather than two.
//
//   Where a region writes this designation and also the name given to the key
//   its data are under, the two refer to the same key.
//
//   An encrypting tool writes the expression into each protected block the
//   designation was used for, followed by the key's encoded value; and a tool
//   reading such a block combines the entity that provided the keys with this
//   designation to reach the key the block is opened with.
//
// All five are preprocessor-stage rules. The keyword and the two-line
// directive carrying it are in src/preprocessor/protect_keywords.cpp; the half
// that reads an encrypting tool's input for the designation, and selects the
// key a region is encrypted under from it, is
// src/preprocessor/protect_processing.cpp; the half that writes the
// designation back into the block it was used for is
// src/preprocessor/protect_envelope_output.cpp; and the reading side --
// consuming the announced line, putting the designation in effect, holding the
// pair of designations to referring to one key, and selecting the key a block
// opens with -- is src/preprocessor/preprocessor_protect_keys.cpp.
//
// Every input below is written as the real `pragma directive syntax of §22.11,
// with the envelopes of §34.5.1 and §34.5.2 delimiting the regions, the entity
// named by §34.5.10's keyword, the key named by §34.5.12's, and every encoded
// value written with §34.5.9's own encoder under the scheme §34.5.9's own
// expression states. A designation is therefore built the way a source text
// builds one, and a region that was encrypted was encrypted because the
// designation really reached a key.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity a region names as having provided the keys its data are under.
constexpr std::string_view kKeyOwner = "acme";

// Another entity, for the inputs that ask what a designation reaches when it is
// read against a list of keys that is not the one it was written under.
constexpr std::string_view kOtherOwner = "globex";

// The public key one of that entity's keys is, as the designation §34.5.13
// writes beneath its keyword. Its length is not a multiple of three, so the
// base64 writing of it ends in the padding character -- which the coding scheme
// this implementation writes its own blocks under has no place for. That is
// what lets an input written under one scheme be shown not to designate
// anything under another.
constexpr std::string_view kPublicKey = "acme-rsa-public-key";

// The key that designation reaches: the one the region's data are really
// encrypted under.
constexpr std::string_view kRegionKey = "acme-region-exchange-key";

// The name given to that same key by §34.5.12's keyword, for the inputs that
// write both designations.
constexpr std::string_view kKeyName = "acme-2026";

// A second key of the same entity, for the input whose two designations reach
// two different keys.
constexpr std::string_view kSecondKey = "acme-some-other-key-entirely";

// An enctype naming no coding scheme this implementation provides. Table 34-2
// leaves further identifiers to the implementation, so a name outside both sets
// stands for no writing at all, and a value under it is the encoded value of
// nothing.
constexpr std::string_view kUnavailableEnctype = "x-no-such-scheme-here";

// The design text sealed inside every region below. Nothing of it survives the
// block-alphabet writing of an encrypted block, so finding it in a tool's
// output is finding a region that was never encrypted, and finding it in a
// preprocessor's output is finding one that was opened.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// The coding scheme a text that stated none is read and written under.
ProtectEncoding BlockEncoding() { return DefaultProtectEncoding(); }

// One of the two Table 34-2 requires of every implementation, for the inputs
// that state a scheme of their own.
ProtectEncoding Base64Encoding() {
  ProtectEncoding encoding;
  encoding.enctype = std::string(kBase64Enctype);
  return encoding;
}

// A user holding one key of `owner`, designated by `designation`.
ProtectKeyList KeyHeldUnder(std::string_view owner,
                            std::string_view designation,
                            std::string_view key = kRegionKey) {
  ProtectKeyList keys;
  keys.Add({std::string(owner), std::string(designation), std::string(key)});
  return keys;
}

// A user holding two of one entity's keys: the one picked out by the name given
// to it, and the one picked out by the public key it is.
ProtectKeyList KeysUnderBothDesignations(std::string_view under_name,
                                         std::string_view under_public) {
  ProtectKeyList keys;
  keys.Add(
      {std::string(kKeyOwner), std::string(kKeyName), std::string(under_name)});
  keys.Add({std::string(kKeyOwner), std::string(kPublicKey),
            std::string(under_public)});
  return keys;
}

// A user holding the same two designations under two entities: under the second
// they pick out one key, and under the first they pick out two different ones.
//
// It is one list rather than two so that a text read against one entity differs
// from the same text read against the other in nothing but the entity. Whatever
// verdict follows is then the entity's doing rather than the key list's.
ProtectKeyList KeysUnderTwoEntities() {
  ProtectKeyList keys;
  keys.Add(
      {std::string(kKeyOwner), std::string(kKeyName), std::string(kRegionKey)});
  keys.Add({std::string(kKeyOwner), std::string(kPublicKey),
            std::string(kSecondKey)});
  keys.Add({std::string(kOtherOwner), std::string(kKeyName),
            std::string(kRegionKey)});
  keys.Add({std::string(kOtherOwner), std::string(kPublicKey),
            std::string(kRegionKey)});
  return keys;
}

// The directive §34.5.10 names the entity with.
std::string NamesKeyOwner(std::string_view owner) {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(owner).append("\"\n");
  return text;
}

// The directive §34.5.12 names one of that entity's keys with.
std::string NamesKeyName(std::string_view keyname) {
  std::string text = "`pragma protect data_keyname=\"";
  text.append(keyname).append("\"\n");
  return text;
}

// The directive §34.5.9 states a coding scheme with.
std::string StatesEncoding(std::string_view enctype) {
  std::string text = "`pragma protect encoding=(enctype=\"";
  text.append(enctype).append("\")\n");
  return text;
}

// The two lines a designation is spelled over: the keyword standing alone, and
// `key` written under `encoding` on the line beneath it.
//
// It serves both sides. A source text designating a key writes these two lines,
// and an encrypting tool writing the designation into the block it was used for
// writes the same two, so the text a tool produced is compared against the same
// spelling an input is built from.
std::string PublicKeyDesignation(std::string_view key,
                                 const ProtectEncoding& encoding) {
  std::string text = "`pragma protect data_public_key\n";
  text.append(EncodeProtectBlock(key, encoding)).append("\n");
  return text;
}

// One encryption envelope: the delimiters of §34.5.1 and §34.5.2 with
// `described` and then `body` between them.
std::string Region(const std::string& described, std::string_view body) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(body);
  text.append("`pragma protect end\n");
  return text;
}

// A decryption envelope as some other tool wrote it: the delimiters of §34.5.3
// and §34.5.4 with `described` between them.
//
// It is written out here rather than produced, because the expressions an
// envelope of this tool's own making carries always stand in one order, and a
// tool reads envelopes it did not produce. What order another producer wrote
// its expressions in is not something a reader gets to settle.
//
// It carries no block, the rule observed through it being about the
// designations an envelope states rather than about what they go on to open.
std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

// The text that stands where the encryption envelopes of `src` were written,
// for an IP author who supplied keys under the names that select them and no
// single key of their own.
std::string Encrypted(const std::string& src, const ProtectKeyList& keys) {
  return EncryptEnvelopes(src, "", keys);
}

// The same, for an IP author who supplied one key of their own and none under a
// name that selects it. That key encrypts every region, whoever a region names.
std::string EncryptedUnderOneKey(const std::string& src, std::string_view key) {
  return EncryptEnvelopes(src, key);
}

// The decryption envelope standing for a region that `described` specifies,
// checked on the way out to be one: the design it was formed from is gone from
// the text.
//
// A round trip that looked only at what came back would pass on a region that
// was never encrypted at all, the design being present in that text for the
// plainest of reasons and no block having been opened to put it there. The
// check is made here rather than in each test because every round trip below
// needs it and none of them is about it.
std::string EnvelopeFor(const std::string& described,
                        const ProtectKeyList& keys) {
  std::string envelope = Encrypted(Region(described, kSealedDesign), keys);
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos);
  return envelope;
}

// The same, for the author who holds one key under no name.
std::string EnvelopeUnderOneKey(const std::string& described,
                                std::string_view key) {
  std::string envelope =
      EncryptedUnderOneKey(Region(described, kSealedDesign), key);
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos);
  return envelope;
}

// A reading of `src` by a tool holding `keys`, with the diagnostics that
// reading raised.
//
// The produced text is where a region that was opened is observed, and the
// diagnostics beside it are where a pair of designations that cannot both be
// the region's key is.
struct ReadUnderKeys {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  ReadUnderKeys(const std::string& src, const ProtectKeyList& keys) {
    PreprocConfig config;
    config.protect_keys = keys;
    Preprocessor pp(mgr, diag, config);
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  // The same, for a user holding one key under no name at all. Names in a text
  // select among keys, and where a user holds one there is nothing to select
  // among, so this is a different state from a list that happens to hold one
  // entry rather than a shorthand for it.
  ReadUnderKeys(const std::string& src, std::string_view key) {
    PreprocConfig config;
    config.protect_key = key;
    Preprocessor pp(mgr, diag, config);
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

// How many times `needle` is written in `text`.
size_t Occurrences(std::string_view text, std::string_view needle) {
  size_t count = 0;
  size_t pos = text.find(needle);
  while (pos != std::string_view::npos) {
    ++count;
    pos = text.find(needle, pos + 1);
  }
  return count;
}

// ---------------------------------------------------------------------------
// The line beneath the keyword holds the encoded value of the public key.
// ---------------------------------------------------------------------------

// The designation reaches a key, and the region is encrypted under it. Nothing
// else in this input names a key at all, so a region whose design has stopped
// being readable is one the line beneath the keyword picked the key for.
TEST(ProtectDataPublicKeyEncryptionInput, TheLineBeneathTheKeywordPicksTheKey) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

// The negative: the same input with a line the scheme in effect never wrote
// standing beneath the keyword. Those characters are the encoded value of
// nothing, so the region designates no key, and a region with no key to be
// encrypted under goes back exactly as the source wrote it.
TEST(ProtectDataPublicKeyEncryptionInput,
     ALineTheSchemeNeverWroteDesignatesNothing) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += "`pragma protect data_public_key\n!! not an encoded value !!\n";
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_NE(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

// The keyword is defined standing alone, so the same name carrying a
// pragma_value is written in a spelling the keyword is not defined with and
// says nothing about the line beneath it. That line is design text, the region
// designates no key, and it goes back as it was written.
TEST(ProtectDataPublicKeyEncryptionInput,
     TheKeywordCarryingAValueAnnouncesNothing) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += "`pragma protect data_public_key=\"against-the-keyword\"\n";
  described += EncodeProtectBlock(kPublicKey, BlockEncoding());
  described += "\n";
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_NE(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

// A designation written where the region can see it but outside its delimiters
// reaches the region all the same. §34.4 makes the scope of these keywords
// lexical, so what is in effect where a region ends is what selects its key,
// whether it was written between the delimiters or ahead of them.
TEST(ProtectDataPublicKeyEncryptionInput,
     ADesignationAheadOfTheRegionSelectsItsKey) {
  std::string src = NamesKeyOwner(kKeyOwner);
  src += PublicKeyDesignation(kPublicKey, BlockEncoding());
  src += Region(std::string(), kSealedDesign);
  std::string encrypted = Encrypted(src, KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

// ---------------------------------------------------------------------------
// The encoding pragma expression in effect settles what the line says.
// ---------------------------------------------------------------------------

// One key written under a scheme the text stated for itself designates the same
// key of the same entity as one written under the default scheme, because what
// travels is the key rather than the characters spelling it.
TEST(ProtectDataPublicKeyEncryptionInput,
     TheStatedSchemeIsWhatTheLineIsReadUnder) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += StatesEncoding(kBase64Enctype);
  described += PublicKeyDesignation(kPublicKey, Base64Encoding());
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

// The negative: the same characters with no expression putting that scheme in
// effect. They are then read under the scheme that stands where nothing was
// stated, which is not the one that wrote them, so they are the encoded value
// of nothing and the region designates no key.
TEST(ProtectDataPublicKeyEncryptionInput,
     TheSameCharactersUnderAnotherSchemeDesignateNothing) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, Base64Encoding());
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_NE(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

// The other negative the encoding in effect has: a scheme this implementation
// provides nothing for. The characters beneath the keyword are then the encoded
// value of nothing at all -- there is no writing to measure them against -- so
// the region designates no key however well formed they are under some other
// scheme, and it goes back as the source wrote it.
TEST(ProtectDataPublicKeyEncryptionInput,
     ASchemeThisToolHasNoneOfDesignatesNothing) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += StatesEncoding(kUnavailableEnctype);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_NE(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
}

// ---------------------------------------------------------------------------
// The keyword and the encoded value are written into the protected block.
// ---------------------------------------------------------------------------

// The two lines stand in the block the designation was used for, in the clear,
// and they stand once: the pair the source wrote went into the encrypted body
// along with the rest of the region, so the pair that can be read is the one
// the encrypting tool wrote out.
TEST(ProtectDataPublicKeyEncryptionOutput,
     TheDesignationIsWrittenIntoTheBlockItWasUsedFor) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  std::string written = PublicKeyDesignation(kPublicKey, BlockEncoding());
  EXPECT_EQ(Occurrences(encrypted, written), 1U);
  EXPECT_LT(encrypted.find("`pragma protect begin_protected"),
            encrypted.find(written));
  EXPECT_LT(encrypted.find(written),
            encrypted.find("`pragma protect end_protected"));
}

// A region that designated no key this way has nothing to write out, so the
// keyword appears nowhere in the block. What is written is the designation that
// was used rather than the keyword as a matter of course.
TEST(ProtectDataPublicKeyEncryptionOutput,
     ARegionDesignatingByNameWritesNoPublicKey) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += NamesKeyName(kKeyName);
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kKeyName));
  EXPECT_NE(encrypted.find("`pragma protect begin_protected"),
            std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect data_public_key"),
            std::string::npos);
}

// The value goes out in the scheme the envelope carrying it declares rather
// than in whichever one the source happened to spell it with. The designation
// here is written before the region states a scheme of its own, so it is read
// under the default and written back out under the one the envelope goes on to
// declare -- and it is the key that crossed, not the characters.
TEST(ProtectDataPublicKeyEncryptionOutput,
     TheValueIsWrittenInTheEnvelopesOwnScheme) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  described += StatesEncoding(kBase64Enctype);
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  EXPECT_NE(encrypted.find(PublicKeyDesignation(kPublicKey, Base64Encoding())),
            std::string::npos);
  EXPECT_EQ(encrypted.find(PublicKeyDesignation(kPublicKey, BlockEncoding())),
            std::string::npos);
}

// Each block the designation was used for gets its own copy, not one copy for
// the text. Two regions designating the same key of the same entity are two
// envelopes, each read on its own by whatever reaches it, so an envelope
// relying on a designation written into the one before it would be unreadable
// wherever the two are separated.
TEST(ProtectDataPublicKeyEncryptionOutput,
     EachBlockTheDesignationWasUsedForCarriesIt) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string src = Region(described, "module first_m; endmodule\n");
  src += Region(described, "module second_m; endmodule\n");
  std::string encrypted = Encrypted(src, KeyHeldUnder(kKeyOwner, kPublicKey));
  std::string written = PublicKeyDesignation(kPublicKey, BlockEncoding());
  EXPECT_EQ(Occurrences(encrypted, "`pragma protect begin_protected"), 2U);
  EXPECT_EQ(Occurrences(encrypted, written), 2U);
  EXPECT_EQ(encrypted.find("module first_m"), std::string::npos);
  EXPECT_EQ(encrypted.find("module second_m"), std::string::npos);
}

// A designation an expression ahead of the region made is written into the
// block all the same. It is as much that region's designation as one written
// between its delimiters, and it is what the region was encrypted under, so a
// block that left it outside would say nothing about the key that opens it --
// which is what a reader reaching the envelope on its own would have to go on.
TEST(ProtectDataPublicKeyEncryptionOutput,
     ADesignationMadeAheadOfTheRegionIsWrittenIntoItsBlock) {
  std::string src = NamesKeyOwner(kKeyOwner);
  src += PublicKeyDesignation(kPublicKey, BlockEncoding());
  src += Region(std::string(), kSealedDesign);
  std::string encrypted = Encrypted(src, KeyHeldUnder(kKeyOwner, kPublicKey));
  std::string written = PublicKeyDesignation(kPublicKey, BlockEncoding());
  // Twice: the source's own two lines, carried across as the bytes they were
  // written with, and the copy the block was given.
  EXPECT_EQ(Occurrences(encrypted, written), 2U);
  EXPECT_LT(encrypted.find("`pragma protect begin_protected"),
            encrypted.rfind(written));
  EXPECT_LT(encrypted.rfind(written),
            encrypted.find("`pragma protect end_protected"));
}

// The identifier naming the cipher stands in the same block as the designation
// and ahead of it. The two together are what says how the data were encrypted
// -- a key designation says nothing about which algorithm it is a designation
// for -- so a reader that has reached the designation has the cipher in hand
// already.
TEST(ProtectDataPublicKeyEncryptionOutput,
     TheCipherIsStatedInTheBlockAheadOfTheDesignation) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string encrypted = Encrypted(Region(described, kSealedDesign),
                                    KeyHeldUnder(kKeyOwner, kPublicKey));
  std::string method = "`pragma protect data_method=\"";
  method.append(kDataMethod).append("\"\n");
  std::string written = PublicKeyDesignation(kPublicKey, BlockEncoding());
  EXPECT_NE(encrypted.find(method), std::string::npos);
  EXPECT_LT(encrypted.find("`pragma protect begin_protected"),
            encrypted.find(method));
  EXPECT_LT(encrypted.find(method), encrypted.find(written));
}

// ---------------------------------------------------------------------------
// The entity and the designation together reach the key a block opens with.
// ---------------------------------------------------------------------------

// The whole round trip: a region whose only designation is the public key one
// of the entity's keys is comes back as the design it was written from. The
// envelope carries the pair, and the reading combines them to reach the key.
TEST(ProtectDataPublicKeyDecryptionInput,
     TheEntityAndThePublicKeyOpenTheBlock) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeyHeldUnder(kKeyOwner, kPublicKey);
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.diag.HasErrors());
}

// The designation is read against the entity written beside it. The same public
// key held for another entity is another key or none, so the pair reaches
// nothing, the block stays closed, and the reading says so.
TEST(ProtectDataPublicKeyDecryptionInput,
     ThePublicKeyIsReadAgainstTheEntityBesideIt) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string envelope =
      EnvelopeFor(described, KeyHeldUnder(kKeyOwner, kPublicKey));
  ReadUnderKeys read(envelope, KeyHeldUnder(kOtherOwner, kPublicKey));
  EXPECT_FALSE(read.Holds("module sealed_m"));
  EXPECT_TRUE(read.diag.HasErrors());
}

// The line the keyword announced is key material of the protected block rather
// than text of the design, so none of it reaches the text the compilation step
// after the preprocessor reads.
TEST(ProtectDataPublicKeyDecryptionInput,
     TheAnnouncedLineIsNotEmittedAsDesign) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeyHeldUnder(kKeyOwner, kPublicKey);
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_FALSE(read.Holds(EncodeProtectBlock(kPublicKey, BlockEncoding())));
  EXPECT_TRUE(read.Holds("module sealed_m"));
}

// The value beneath the keyword is read under whichever scheme the envelope
// carrying it declares, not under the one this tool writes its own blocks in.
// The whole round trip runs under a scheme the region asked for, so the
// designation was written, carried and read back under that scheme rather than
// merely produced in it.
TEST(ProtectDataPublicKeyDecryptionInput,
     AnEnvelopeDeclaringAnotherSchemeIsReadBackUnderIt) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += StatesEncoding(kBase64Enctype);
  described += PublicKeyDesignation(kPublicKey, Base64Encoding());
  ProtectKeyList keys = KeyHeldUnder(kKeyOwner, kPublicKey);
  std::string envelope = EnvelopeFor(described, keys);
  EXPECT_NE(envelope.find("enctype=\"base64\""), std::string::npos);
  ReadUnderKeys read(envelope, keys);
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.diag.HasErrors());
}

// A user holding one key under no name at all has nothing for a designation to
// select among, so the block opens under that key and the designation the
// envelope carries selects nothing. The designation is still written into the
// block, because what a region was designated by does not stop being part of
// the envelope's description of itself when a particular reader had no use for
// it.
TEST(ProtectDataPublicKeyDecryptionInput,
     AReaderHoldingOneKeyOpensTheBlockWithoutSelecting) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  std::string envelope = EnvelopeUnderOneKey(described, kRegionKey);
  EXPECT_NE(envelope.find(PublicKeyDesignation(kPublicKey, BlockEncoding())),
            std::string::npos);
  ReadUnderKeys read(envelope, kRegionKey);
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// Where both designations are written, they refer to the same key.
// ---------------------------------------------------------------------------

// Two designations reaching one key of the entity are the one key picked out
// twice, which is what the subclause asks for, so nothing is reported.
TEST(ProtectDataPublicKeyDecryptionInput,
     TwoDesignationsReachingOneKeyAreAccepted) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += NamesKeyName(kKeyName);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeysUnderBothDesignations(kRegionKey, kRegionKey);
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.diag.HasErrors());
}

// The negative: two designations of the same entity's keys reaching two
// different keys. They are alternative ways of picking one key out rather than
// two keys to be under at once, so the region has asked for a key its data
// cannot be under, and it is reported.
TEST(ProtectDataPublicKeyDecryptionInput,
     TwoDesignationsReachingTwoKeysAreReported) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += NamesKeyName(kKeyName);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeysUnderBothDesignations(kRegionKey, kSecondKey);
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_TRUE(read.diag.HasErrors());
}

// The disagreement is about the pair rather than about the block: the name
// written for the key still reaches the key the region was encrypted under, so
// the design comes back even as the reading reports that the two designations
// cannot both be its key.
TEST(ProtectDataPublicKeyDecryptionInput,
     TheDisagreementLeavesTheBlockReadable) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += NamesKeyName(kKeyName);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeysUnderBothDesignations(kRegionKey, kSecondKey);
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_TRUE(read.Holds("module sealed_m"));
}

// Both designations are read against the entity in effect beside them, so the
// entity is what decides whether they reach one key. Here they reach one key of
// the entity the region names, and the pair stands -- although the very same
// two designations, read against the other entity in the same list of keys,
// reach two.
TEST(ProtectDataPublicKeyDecryptionInput,
     TheEntityInEffectDecidesWhichKeysThePairIsReadAgainst) {
  std::string described = NamesKeyOwner(kOtherOwner);
  described += NamesKeyName(kKeyName);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeysUnderTwoEntities();
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.diag.HasErrors());
}

// The pair is held to referring to one key whichever of the two was written
// first. Here the name arrives after the line carrying the public key, so it is
// the name that completes the pair, and the disagreement is reached from there
// rather than from the line beneath the keyword.
TEST(ProtectDataPublicKeyDecryptionInput,
     TheNameWrittenAfterThePublicKeyCompletesThePair) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  described += NamesKeyName(kKeyName);
  ReadUnderKeys read(ForeignEnvelope(described),
                     KeysUnderBothDesignations(kRegionKey, kSecondKey));
  EXPECT_EQ(read.diag.ErrorCount(), 1U);
}

// The same envelope whose two designations reach one key raises nothing,
// which is what keeps the report above from being something the reversed order
// produces on its own.
TEST(ProtectDataPublicKeyDecryptionInput,
     TheReversedOrderAcceptsAPairReachingOneKey) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  described += NamesKeyName(kKeyName);
  ReadUnderKeys read(ForeignEnvelope(described),
                     KeysUnderBothDesignations(kRegionKey, kRegionKey));
  EXPECT_EQ(read.diag.ErrorCount(), 0U);
}

// A tool holding a key under only one of the two designations has no second key
// for the first to disagree with, so the pair is left as the region wrote it.
// An input that cannot fail either way would say nothing about the rule, which
// is why the same source text is read here against a shorter list of keys.
TEST(ProtectDataPublicKeyDecryptionInput,
     OneDesignationReachingNothingDecidesNothing) {
  std::string described = NamesKeyOwner(kKeyOwner);
  described += NamesKeyName(kKeyName);
  described += PublicKeyDesignation(kPublicKey, BlockEncoding());
  ProtectKeyList keys = KeyHeldUnder(kKeyOwner, kKeyName);
  ReadUnderKeys read(EnvelopeFor(described, keys), keys);
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.diag.HasErrors());
}

}  // namespace
