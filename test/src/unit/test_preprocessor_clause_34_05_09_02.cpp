// §34.5.9.2 Description, for the protect pragma keyword that settles the
// writing every encoded value of a protected envelope is carried as. The syntax
// block above it settles how the expression is spelled; this one settles what a
// tool does with one, under the three headings the subclause writes its rules
// under.
//
// ENCRYPTION INPUT. The expression settles how the content of a data_block, a
// digest_block and a key_block is written, and that writing is what lets every
// byte an encryption produces travel as text. An expression standing in the
// input stream settles how the output is written. Three subkeywords carry the
// parts of it:
//
//   enctype names the method the writing is calculated by. Table 34-2 sets four
//   identifiers aside as string values of this name, each bound to a published
//   algorithm: uuencode, standing for the historical algorithm of IEEE Std
//   1003.1, and base64, standing for IETF RFC 2045, are required of every
//   implementation; quoted-printable, standing for IETF RFC 2045, and raw,
//   standing for the identity transformation that performs no writing at all
//   and leaves the data free to hold characters that cannot be printed, are
//   optional. An implementation offering an optional one offers it under that
//   identifier rather than one of its own, and further identifiers, with the
//   algorithms behind them, are the implementation's.
//
//   line_length is the most characters one line of a data_block may hold once
//   the writing has been applied, the breaks being there so that ordinary text
//   tools can handle what an encryption produced.
//
//   bytes is how much data the block held before any writing was applied to it
//   and before any line was broken. An encrypting tool ignores it in its input.
//
// ENCRYPTION OUTPUT. The directive is written into each protected envelope, so
// that the writing the encrypting tool used is stated rather than guessed at. A
// tool may write the data under a scheme even where the input asked for none,
// and states the expression that goes with what it did. It states, against the
// bytes name, how much data each block it writes stands for. Every encoded
// value of the envelope goes under that one scheme -- the data block, the
// public key the data are under, the key that decrypts them, the digest block,
// the key block and the public key the region's own keys are under -- and a
// text wanting one of them written differently states a further expression
// ahead of it.
//
// DECRYPTION INPUT. A tool reading an envelope takes two things from the
// directive: the algorithm the characters were written by, and how much data
// they stand for.
//
// All of it is preprocessor-stage. src/preprocessor/protect_encoding.cpp holds
// Table 34-2 and reads a value into the three parts it is spelled with;
// src/preprocessor/protect_encoding_codecs.cpp carries the four algorithms;
// src/preprocessor/protect_processing.cpp is the encrypting half, which takes
// the scheme a text asked for and reads the region's own encoded values under
// it; src/preprocessor/protect_envelope_output.cpp writes the directive into
// each envelope and states the count of each block, with
// src/preprocessor/protect_digest_block.cpp and
// src/preprocessor/protect_key_block.cpp doing the same for the blocks they
// write; src/preprocessor/protect_processing_cipher.cpp applies the writing to
// what the cipher produced; and
// src/preprocessor/preprocessor_protect_keys.cpp is where a reading takes the
// algorithm and the count back out.
//
// The inputs are the real syntax of the constructs this rule consumes.
// §34.5.1.1's and §34.5.2.1's words delimit every region handed to the
// encrypting half, and §34.5.3.1's and §34.5.4.1's words delimit the envelopes
// that half produces and the envelopes a reading is then handed -- an encoded
// value has no standing outside one. §34.5.7's encrypt_agent stands in the
// clear on each of those envelopes beside the expression under test, which is
// what the output rule means by the writing the encrypting tool used. Beyond
// the dependencies, §34.5.23's key_keyowner with §34.5.13's and §34.5.26's
// public-key designations are how a region names a key by an encoded value,
// §34.5.27's key_block and §34.5.14's key inside it are two more of the values
// governed here, §34.5.22's digest_block asks for the second block an envelope
// carries, and §34.5.15's data_block is where the region's own text ends up.
// Every text below is written as directive syntax and driven through the
// encrypting half, the preprocessor, or both in turn.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The key an IP author hands the encrypting half, and hands back to a tool
// reading what that half produced. Without one nothing is sealed and nothing is
// opened, so a reading that found no design text could not be told apart from a
// key that was never supplied.
constexpr std::string_view kExchangeKey = "globex-exchange-key";

// The design a region seals. Nothing of it survives any of the alphabets a
// block is written in, so finding it outside a block is finding a region that
// was never sealed, and finding it in what a reading produced is finding a
// block that opened.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// A second design, for the text that writes two regions. Two envelopes come
// back from such a text, and each has to describe itself: a rule about what
// every envelope carries is not observed by looking at one.
constexpr std::string_view kSecondDesign = "module sealed_n; endmodule\n";

// A design chosen to make the writing work for its living. It carries the one
// character that would end the value a block travels as, and a byte that cannot
// be printed at all, so a block recording it holds bytes no source line could
// carry until the writing has been applied.
constexpr std::string_view kAwkwardDesign =
    "module sealed_q; // \" \x01\nendmodule\n";

// Where a reading meets the block an envelope carries. Everything a block is
// read under has to stand ahead of this, so a directive written here is the
// last word on the writing in effect where the block is opened.
constexpr std::string_view kBlockOpening = "`pragma protect data_block=\"";

// §34.5.3.1's word, as the encrypting half writes it. It is where one envelope
// starts, so it is also how a text carrying two of them is cut in half.
constexpr std::string_view kProtectedOpening =
    "`pragma protect begin_protected";

// The keywords that speak for the line beneath them, each carrying one of the
// encoded values §34.5.9.2 lists. Reading a value means finding the line after
// one of these: §34.5.13's designation of the key the data are under,
// §34.5.26's designation of the key the region's own keys are under,
// §34.5.27's block carrying those keys, and §34.5.14's key inside it.
constexpr std::string_view kDataPublicKeyLine =
    "`pragma protect data_public_key\n";
constexpr std::string_view kKeyPublicKeyLine =
    "`pragma protect key_public_key\n";
constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";
constexpr std::string_view kDataDecryptKeyLine =
    "`pragma protect data_decrypt_key\n";

// The opening of any directive this subclause's keyword is written on.
constexpr std::string_view kAnyEncoding = "`pragma protect encoding=";

// §34.5.22's expression, which serves twice over in one text and is spelled the
// same way both times. Written between a region's delimiters it asks for a
// message digest, which is what makes an envelope carry a second block; written
// by the tool into the envelope it announces the digest on the line beneath it.
//
// A request travels into the block along with the design, so the only directive
// of this name left standing in the clear is the one the tool wrote.
constexpr std::string_view kDigestBlockLine = "`pragma protect digest_block\n";

// The entity that provided the key a region's own keys are under, as §34.5.23
// names it, and the key that entity holds.
constexpr std::string_view kKeyProvider = "acme";
constexpr std::string_view kProviderKey = "acme-provider-key";

// The public key a region designates that entity's key by, as §34.5.26 has it
// written: the keyword on one line and the key's encoded value on the next.
//
// It holds a space, the one character of it the four tabulated algorithms treat
// four different ways -- as itself, as an escape, as nothing recognizable, and
// as part of a group. A designation of letters alone would come out of raw and
// quoted-printable alike, and neither could then be told from the other.
constexpr std::string_view kDesignatedKey = "acme public";

// That same value written by each of the algorithms Table 34-2 names, spelled
// out here rather than produced by the tool under test: a designation this tool
// wrote for itself would be read back by whatever writing it happens to
// perform, while these are what the published algorithms produce. The identity
// transformation is not among them -- its row performs no writing, so the
// designation is the key and kDesignatedKey serves for both.
constexpr std::string_view kDesignationInBase64 = "YWNtZSBwdWJsaWM=";
constexpr std::string_view kDesignationInUuencode = "+86-M92!P=6)L:6,`";
constexpr std::string_view kDesignationInQuotedPrintable = "acme=20public";

// A designation holding a character that cannot be printed, for the one row of
// the table that admits such data. Written under any other scheme these bytes
// would be an escape or an alphabet member; written under this one they are the
// data.
constexpr std::string_view kUnprintableDesignation = "acme\x01public";

// An identifier no row of Table 34-2 names and this implementation does not
// define either, so it stands for no writing at all.
constexpr std::string_view kUnprovidedEnctype = "x-nobody-provides-this";

// Whether `where` writes `what` anywhere in it.
bool Holds(std::string_view where, std::string_view what) {
  return where.find(what) != std::string_view::npos;
}

// How many times `where` writes `what`, counting the writings that do not
// overlap.
size_t TimesWritten(std::string_view where, std::string_view what) {
  size_t written = 0;
  for (size_t at = where.find(what); at != std::string_view::npos;
       at = where.find(what, at + what.size())) {
    ++written;
  }
  return written;
}

// The directive this subclause defines, carrying `list` as the pragma_value
// written against the keyword.
std::string StatesEncoding(std::string_view list) {
  std::string directive(kAnyEncoding);
  directive.append(list).append("\n");
  return directive;
}

// The shortest value the keyword is defined with: the scheme alone, written as
// the string §34.5.9.1 calls for.
std::string NamesScheme(std::string_view enctype) {
  std::string list = "(enctype=\"";
  list.append(enctype).append("\")");
  return StatesEncoding(list);
}

// The text one region encloses: whatever it writes about itself, then the
// design it seals. The design comes last so that a line the encryption passed
// over is a line that went into the block ahead of it.
std::string RegionBody(std::string_view inside) {
  std::string body(inside);
  body.append(kSealedDesign);
  return body;
}

// One encryption envelope: §34.5.1.1's and §34.5.2.1's words with that body
// between them.
std::string RegionHolding(std::string_view inside) {
  std::string region = "`pragma protect begin\n";
  region.append(RegionBody(inside));
  region.append("`pragma protect end\n");
  return region;
}

// The expression an encrypting tool writes to state how much data one block
// stands for, as it stands in an envelope: the count against the bytes name,
// with the parenthesis that closes the list behind it. The parenthesis is part
// of what is looked for, a count of thirty-one being written by the same
// characters that begin a count of three hundred and ten.
std::string TheCountOf(size_t bytes) {
  std::string counted = "bytes=";
  counted.append(std::to_string(bytes)).append(")");
  return counted;
}

// What a reading is configured with for opening the protected regions an input
// carries, which is the key and nothing besides.
PreprocConfig HoldingTheKey() {
  PreprocConfig config;
  config.protect_key = std::string(kExchangeKey);
  return config;
}

// The envelope the encrypting half leaves where `source` wrote its regions,
// checked on the way out to be one: the design it was formed from is gone from
// the text.
//
// A round trip that looked only at what came back would pass on a region that
// was never sealed at all, the design being present in that text for the
// plainest of reasons and no block having been opened to put it there.
std::string EnvelopeOf(const std::string& source) {
  std::string envelope = EncryptEnvelopes(source, kExchangeKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign));
  return envelope;
}

// The envelope produced from one region writing `inside` between its
// delimiters.
std::string EnvelopeAround(std::string_view inside) {
  return EnvelopeOf(RegionHolding(inside));
}

// The characters recording one envelope's sealed region: what stands between
// the quotation marks of its data_block expression, and empty where the text
// carries no such expression.
std::string DataBlockOf(std::string_view envelope) {
  size_t opens = envelope.find(kBlockOpening);
  if (opens == std::string_view::npos) return {};
  size_t from = opens + kBlockOpening.size();
  size_t to = envelope.find('"', from);
  if (to == std::string_view::npos) return {};
  return std::string(envelope.substr(from, to - from));
}

// The part of `text` from where its first protected envelope opens. Text
// outside an envelope is carried across as the bytes it was written with, so a
// directive the source wrote ahead of a region is still standing in what comes
// back, and a search of the whole text would take it for the tool's.
std::string ProtectedPartOf(std::string_view text) {
  size_t opens = text.find(kProtectedOpening);
  if (opens == std::string_view::npos) return {};
  return std::string(text.substr(opens));
}

// The whole of the line standing after `opening`, which is where the keywords
// that speak for the line beneath them put their encoded value.
std::string LineAfter(std::string_view text, std::string_view opening) {
  size_t stands = text.find(opening);
  if (stands == std::string_view::npos) return {};
  size_t from = stands + opening.size();
  size_t to = text.find('\n', from);
  if (to == std::string_view::npos) return {};
  return std::string(text.substr(from, to - from));
}

// The same envelope with `directive` written into it immediately ahead of the
// expression carrying its block. §34.4 has a value in effect over the text
// after it, so a directive placed here is the one the block is read under
// whatever the envelope stated about itself further up.
std::string EnvelopeReadUnder(std::string_view directive) {
  std::string envelope = EnvelopeAround("");
  size_t block = envelope.find(kBlockOpening);
  EXPECT_NE(block, std::string::npos);
  return envelope.insert(block, std::string(directive));
}

// The same envelope with `directive` written in at the other end of it, on the
// line after the word that opens the envelope. Everything the envelope says
// about itself, and everything each of its fields says, still stands after it.
std::string EnvelopeOpeningWith(std::string_view directive) {
  std::string envelope = EnvelopeAround("");
  size_t opens = envelope.find(kProtectedOpening);
  EXPECT_NE(opens, std::string::npos);
  size_t ends = envelope.find('\n', opens);
  EXPECT_NE(ends, std::string::npos);
  return envelope.insert(ends + 1, std::string(directive));
}

// A text writing two regions one after the other, each sealing a design of its
// own.
std::string TwoRegions() {
  std::string source = "`pragma protect begin\n";
  source.append(kSealedDesign).append("`pragma protect end\n");
  source.append("`pragma protect begin\n");
  source.append(kSecondDesign).append("`pragma protect end\n");
  return source;
}

// A region designating the key its data are to be encrypted under by that key's
// encoded value, as §34.5.13 has such a designation written: the keyword
// standing alone and the value on the line beneath it, read under the writing
// the region names above it.
std::string RegionDesignatingTheDataKey(std::string_view enctype,
                                        std::string_view encoded) {
  std::string inside(NamesScheme(enctype));
  inside.append(kDataPublicKeyLine).append(encoded).append("\n");
  return RegionHolding(inside);
}

// A region that reaches no key by name and designates one instead, as §34.5.26
// has such a designation written: the entity that provided it, the writing the
// designation is spelled in, the keyword standing alone, and the encoded value
// on the line beneath it.
//
// The scheme is stated between the region's delimiters rather than ahead of
// them, so the line carrying the designation is read under a writing the region
// itself named.
std::string RegionDesignating(std::string_view enctype,
                              std::string_view encoded) {
  std::string inside = "`pragma protect key_keyowner=\"";
  inside.append(kKeyProvider).append("\"\n");
  inside.append(NamesScheme(enctype));
  inside.append("`pragma protect key_public_key\n");
  inside.append(encoded).append("\n");
  return RegionHolding(inside);
}

// What the encrypting half leaves where that region was written, for a tool
// holding the provider's key under `held`.
//
// Nothing else can seal this region: it names no key of its own and the tool is
// handed no exchange key, so the only way to a key is the designation beneath
// the keyword, and reaching it means reading that line out of the writing the
// region named. A region left with its design in the clear reached nothing.
std::string SealedByDesignation(std::string_view enctype,
                                std::string_view encoded,
                                std::string_view held) {
  ProtectKeyList keys;
  keys.Add({std::string(kKeyProvider), std::string(held),
            std::string(kProviderKey)});
  return EncryptEnvelopes(RegionDesignating(enctype, encoded), "", keys);
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: the scheme a text names is the writing its block gets.
// ---------------------------------------------------------------------------

// A region naming one of the required identifiers, driven through the
// encrypting half. The characters its envelope carries are read back by that
// identifier's algorithm alone -- not by this tool's reading of the envelope,
// which would prove only that the tool agrees with itself -- and the bytes
// they give up are the bytes the region's cipher produced.
//
// This is the whole of the encryption-input rule in one input: a scheme was
// named, and the block content really is what that scheme writes.
TEST(ProtectEncodingEncryptionInput, TheSchemeARegionNamesWritesItsBlock) {
  std::string envelope = EnvelopeAround(NamesScheme(kBase64Enctype));
  ASSERT_TRUE(Holds(envelope, "enctype=\"base64\""));
  std::string block;
  ASSERT_TRUE(
      DecodeProtectBlock(DataBlockOf(envelope), kBase64Enctype, &block));
  std::string recovered;
  EXPECT_TRUE(DecryptProtectedBlock(block, kExchangeKey, &recovered));
  EXPECT_TRUE(Holds(recovered, kSealedDesign));
}

// The same block read by another of the tabulated algorithms. The identity
// transformation reads anything, so it gives up bytes rather than refusing --
// and those bytes are the characters rather than what the characters stand for,
// so the cipher does not recognize them as a block it produced.
//
// Without this pairing the reading above would be met by a tool that wrote its
// blocks one way whatever a text named, the scheme stated and used nowhere.
TEST(ProtectEncodingEncryptionInput, TheBlockIsNotTheWritingOfAnotherScheme) {
  std::string envelope = EnvelopeAround(NamesScheme(kBase64Enctype));
  std::string block;
  ASSERT_TRUE(DecodeProtectBlock(DataBlockOf(envelope), kRawEnctype, &block));
  std::string recovered;
  EXPECT_FALSE(DecryptProtectedBlock(block, kExchangeKey, &recovered));
}

// The expression standing in the input stream ahead of the region rather than
// inside it. The rule is about an expression present in the input, and §34.4
// makes the scope of one lexical, so a scheme named before the design was ever
// opened is the scheme that design's block is written under.
//
// The two positions are read by different parts of the encrypting half -- one
// is carried into the region when it opens, the other is taken off a line the
// region encloses -- so a tool passing the test above may still lose this one.
TEST(ProtectEncodingEncryptionInput, ASchemeNamedAheadOfARegionWritesItsBlock) {
  std::string source(NamesScheme(kBase64Enctype));
  source.append(RegionHolding(""));
  std::string envelope = EnvelopeOf(source);
  ASSERT_TRUE(Holds(envelope, "enctype=\"base64\""));
  std::string block;
  ASSERT_TRUE(
      DecodeProtectBlock(DataBlockOf(envelope), kBase64Enctype, &block));
  std::string recovered;
  EXPECT_TRUE(DecryptProtectedBlock(block, kExchangeKey, &recovered));
  EXPECT_TRUE(Holds(recovered, kSealedDesign));
}

// The count written where the subclause says a count is ignored. The region
// states one that no block of it could hold, alongside a scheme that is
// honored, so the same expression carries a part that is acted on and a part
// that is not.
//
// What the envelope states is the size of the block the tool wrote, and the
// number the region asked for is nowhere in it. A tool taking the input's count
// would publish a description of its own block that the block contradicts, and
// the next reading of that envelope would refuse it.
TEST(ProtectEncodingEncryptionInput, ACountWrittenInARegionReachesNoEnvelope) {
  std::string inside(
      StatesEncoding("(enctype=\"base64\", line_length=8, bytes=1)"));
  std::string envelope = EnvelopeAround(inside);
  size_t held = ProtectedRegionBlockSize(RegionBody(inside));
  EXPECT_TRUE(Holds(envelope, "enctype=\"base64\""));
  EXPECT_TRUE(Holds(envelope, TheCountOf(held)));
  EXPECT_FALSE(Holds(envelope, TheCountOf(1)));
}

// The same disregarded count at the other position an expression can stand in:
// ahead of the region rather than inside it. §34.4's lexical scope carries it
// in as much as one written between the delimiters, so it reaches the
// encrypting half by the path the scheme itself takes -- and is dropped there.
//
// The envelope is searched rather than the whole text: a directive outside a
// region is carried across unchanged, so the source's own line is still in the
// output and a reading of the text whole would take it for the tool's.
TEST(ProtectEncodingEncryptionInput,
     ACountWrittenAheadOfARegionReachesNoEnvelope) {
  std::string source(StatesEncoding("(enctype=\"base64\", bytes=1)"));
  source.append(RegionHolding(""));
  std::string envelope = ProtectedPartOf(EnvelopeOf(source));
  ASSERT_FALSE(envelope.empty());
  EXPECT_TRUE(Holds(envelope, "enctype=\"base64\""));
  EXPECT_TRUE(
      Holds(envelope, TheCountOf(ProtectedRegionBlockSize(kSealedDesign))));
  EXPECT_FALSE(Holds(envelope, TheCountOf(1)));
}

// The pairing that says the ignoring belongs to the encryption input rather
// than to the count itself: the same disagreeing count, written this time into
// an envelope a reading is handed, is measured against the block standing after
// it and the reading refuses that block.
//
// One number, two positions, two treatments. Without the pair, a tool that took
// no notice of the count anywhere would pass the test above. The control for
// this half is EveryEnvelopeStatesItsOwnWriting, which hands a reading the very
// envelope this one alters and gets the design back without a word: what the
// refusal turns on is the count written in, and nothing else about the text.
TEST(ProtectEncodingEncryptionInput,
     TheSameCountIsActedOnWhenAnEnvelopeIsRead) {
  std::string list = "(enctype=\"";
  list.append(DefaultProtectEncoding().enctype).append("\", bytes=1)");
  PreprocFixture f;
  std::string read =
      Preprocess(EnvelopeReadUnder(StatesEncoding(list)), f, HoldingTheKey());
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_FALSE(Holds(read, "module sealed_m"));
}

// ---------------------------------------------------------------------------
// Table 34-2: the identifiers, and the algorithms behind them.
// ---------------------------------------------------------------------------

// The table itself, row by row and in the order it lists them. Four identifiers
// are set aside, spelled exactly as the table spells them, and each row also
// records whether the standard requires the algorithm behind it of every
// implementation.
TEST(ProtectEncodingTable, TheTableSetsFourIdentifiersAside) {
  auto rows = ProtectEncodingAlgorithms();
  ASSERT_EQ(rows.size(), 4U);
  EXPECT_EQ(rows[0].enctype, "uuencode");
  EXPECT_EQ(rows[1].enctype, "base64");
  EXPECT_EQ(rows[2].enctype, "quoted-printable");
  EXPECT_EQ(rows[3].enctype, "raw");
}

// The table's third column, which is the whole reason the first one is worth
// writing: each identifier stands for one published algorithm, named beside it.
// Every row names one, and no two rows name the same one -- an identifier
// sharing another's algorithm would be an identifier standing for nothing of
// its own, and a text choosing between the two would be choosing nothing.
TEST(ProtectEncodingTable, EachRowNamesAnAlgorithmOfItsOwn) {
  auto rows = ProtectEncodingAlgorithms();
  ASSERT_EQ(rows.size(), 4U);
  for (size_t row = 0; row < rows.size(); ++row) {
    EXPECT_FALSE(rows[row].algorithm.empty());
    for (size_t other = row + 1; other < rows.size(); ++other) {
      EXPECT_NE(rows[row].algorithm, rows[other].algorithm);
    }
  }
}

// The required/optional column, and what being required costs an
// implementation: the two identifiers the table marks required name algorithms
// this tool provides, and it provides the two optional ones as well -- which
// the table permits and does not ask for.
//
// The negative alongside them is the identifier belonging to no row. The
// subclause leaves further identifiers to the implementation, so this tool
// defines one for the writing it performs where a text asked for nothing; it is
// available without being one of the four the standard set aside.
TEST(ProtectEncodingTable, TheRequiredIdentifiersAreProvidedAndSoAreTheRest) {
  EXPECT_TRUE(IsRequiredProtectEncodingAlgorithm(kUuencodeEnctype));
  EXPECT_TRUE(IsRequiredProtectEncodingAlgorithm(kBase64Enctype));
  EXPECT_FALSE(IsRequiredProtectEncodingAlgorithm(kQuotedPrintableEnctype));
  EXPECT_FALSE(IsRequiredProtectEncodingAlgorithm(kRawEnctype));
  EXPECT_TRUE(ProtectEncodingIsAvailable(kQuotedPrintableEnctype));
  EXPECT_TRUE(ProtectEncodingIsAvailable(kRawEnctype));
}

// The implementation's own identifier, which is what the last sentence of the
// enctype paragraph leaves a tool free to define. It stands for a writing this
// tool performs and for no row of the table, so a reading has it available
// without the standard having said anything about it.
TEST(ProtectEncodingTable, TheToolsOwnIdentifierIsNoneOfTheTabulatedFour) {
  EXPECT_FALSE(IsProtectEncodingAlgorithm(kBlockEnctype));
  EXPECT_TRUE(ProtectEncodingIsAvailable(kBlockEnctype));
  EXPECT_FALSE(ProtectEncodingIsAvailable(kUnprovidedEnctype));
}

// The first required identifier, driven through the encrypting half on a real
// designation. The line beneath §34.5.26's keyword is the encoded value of a
// key, so reading it means applying RFC 2045's algorithm to characters no part
// of this tool wrote -- and the key it yields is the one the tool holds, so the
// region is sealed and its keys travel in a key block.
TEST(ProtectEncodingTable, TheRequiredBase64IdentifierReadsADesignation) {
  std::string sealed =
      SealedByDesignation(kBase64Enctype, kDesignationInBase64, kDesignatedKey);
  EXPECT_FALSE(Holds(sealed, kSealedDesign));
  EXPECT_TRUE(Holds(sealed, kKeyBlockLine));
}

// The second required identifier, on the same designation written by the
// historical algorithm of IEEE Std 1003.1 instead: a count character at the
// head of the line and the data six bits to a character after it. The value the
// two algorithms carry is one value, so the key reached is the same key and the
// region is sealed the same way.
TEST(ProtectEncodingTable, TheRequiredUuencodeIdentifierReadsADesignation) {
  std::string sealed = SealedByDesignation(
      kUuencodeEnctype, kDesignationInUuencode, kDesignatedKey);
  EXPECT_FALSE(Holds(sealed, kSealedDesign));
  EXPECT_TRUE(Holds(sealed, kKeyBlockLine));
}

// The first optional identifier. An implementation offering it is required to
// offer it under this spelling, so the observation is that this spelling
// reaches RFC 2045's other algorithm: the escape in the middle of the line
// stands for the space in the middle of the key, and nothing but that algorithm
// turns the one into the other.
TEST(ProtectEncodingTable,
     TheOptionalQuotedPrintableIdentifierReadsADesignation) {
  std::string sealed = SealedByDesignation(
      kQuotedPrintableEnctype, kDesignationInQuotedPrintable, kDesignatedKey);
  EXPECT_FALSE(Holds(sealed, kSealedDesign));
  EXPECT_TRUE(Holds(sealed, kKeyBlockLine));
}

// The second optional identifier, and with it one line standing for two
// different values under two identifiers -- which is what says an identifier is
// consulted rather than assumed. The row for the identity transformation has no
// writing performed, so the line is the value; the characters here are those of
// the base64 designation, and declared that way they are instead the key name
// those characters stand for.
//
// The tool holds its key under the characters themselves, so the reading that
// performs no writing reaches it and the reading that performs RFC 2045's does
// not. The first half is this row's plain positive as much as the contrast: a
// designation read literally is what reaching that key means.
TEST(ProtectEncodingTable, TheSameLineStandsForAnotherValueUnderRaw) {
  std::string as_written = SealedByDesignation(
      kRawEnctype, kDesignationInBase64, kDesignationInBase64);
  std::string as_base64 = SealedByDesignation(
      kBase64Enctype, kDesignationInBase64, kDesignationInBase64);
  EXPECT_FALSE(Holds(as_written, kSealedDesign));
  EXPECT_TRUE(Holds(as_base64, kSealedDesign));
}

// The rest of the raw row: the data such a block carries may hold characters
// that cannot be printed. A designation carrying one reaches the key held under
// it, the byte having travelled through the reading as data rather than as an
// escape or an alphabet member.
TEST(ProtectEncodingTable, ARawDesignationMayHoldAnUnprintableCharacter) {
  std::string sealed = SealedByDesignation(kRawEnctype, kUnprintableDesignation,
                                           kUnprintableDesignation);
  EXPECT_FALSE(Holds(sealed, kSealedDesign));
  EXPECT_TRUE(Holds(sealed, kKeyBlockLine));
}

// The negative the four rows are read against: an identifier no row names and
// this implementation has not defined. It stands for no writing, so the line
// beneath the keyword stands for nothing, the designation reaches no key, and
// the region goes back exactly as it was written -- design and all.
//
// The input differs from the base64 test above in the identifier alone.
TEST(ProtectEncodingTable, AnIdentifierNothingProvidesReadsNoDesignation) {
  std::string untouched = SealedByDesignation(
      kUnprovidedEnctype, kDesignationInBase64, kDesignatedKey);
  EXPECT_TRUE(Holds(untouched, kSealedDesign));
  EXPECT_FALSE(Holds(untouched, kKeyBlockLine));
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: what the envelope states about its own writing.
// ---------------------------------------------------------------------------

// A region asking for nothing at all. The tool writes the data under a scheme
// anyway, which the subclause permits, and states the expression that goes with
// what it did -- so an envelope always carries this directive and a reader
// never has to guess.
TEST(ProtectEncodingEncryptionOutput, EveryEnvelopeStatesItsOwnWriting) {
  std::string envelope = EnvelopeAround("");
  EXPECT_TRUE(Holds(envelope, kAnyEncoding));
  std::string named = "enctype=\"";
  named.append(DefaultProtectEncoding().enctype).append("\"");
  EXPECT_TRUE(Holds(envelope, named));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, "module sealed_m"));
}

// The count the tool generates, against the block it describes. It is of the
// data the block held before any writing was applied, so it is neither the
// length of the region's text -- a block records more than the text -- nor the
// number of characters the block was written as.
//
// Both comparisons are needed. Against the text alone a tool stating the
// characters' length would pass; against the characters alone a tool stating
// the text's length would.
TEST(ProtectEncodingEncryptionOutput, TheCountIsOfTheDataAndNotOfTheWriting) {
  std::string envelope = EnvelopeAround("");
  EXPECT_TRUE(
      Holds(envelope, TheCountOf(ProtectedRegionBlockSize(kSealedDesign))));
  EXPECT_NE(ProtectedRegionBlockSize(kSealedDesign), kSealedDesign.size());
  EXPECT_NE(ProtectedRegionBlockSize(kSealedDesign),
            DataBlockOf(envelope).size());
}

// An envelope carrying two blocks, the second being the digest §34.5.22 asks
// for. The count belongs to one block rather than to the envelope, so the tool
// writes an expression ahead of each of them and states each block's own size.
//
// Three directives go out: the one describing the envelope, which states the
// writing without describing any block, and one ahead of each block. That is
// also the shape a text needs to ask for one field to be written differently
// from another, an expression standing ahead of each field.
TEST(ProtectEncodingEncryptionOutput, EachBlockOfAnEnvelopeStatesItsOwnCount) {
  std::string envelope = EnvelopeAround(kDigestBlockLine);
  size_t held = ProtectedRegionBlockSize(RegionBody(kDigestBlockLine));
  ASSERT_TRUE(Holds(envelope, kDigestBlockLine));
  EXPECT_EQ(TimesWritten(envelope, kAnyEncoding), 3U);
  EXPECT_EQ(TimesWritten(envelope, "bytes="), 2U);
  EXPECT_EQ(TimesWritten(envelope, TheCountOf(held)), 1U);
}

// The same envelope with a scheme named for it. Every encoded value it carries
// is written under the one scheme, so all three expressions name it -- and the
// digest, which is a block of its own written by a different part of the tool
// from the data block, gives its bytes up to that scheme's algorithm.
TEST(ProtectEncodingEncryptionOutput, EveryBlockIsWrittenUnderTheOneScheme) {
  std::string inside(kDigestBlockLine);
  inside.append(NamesScheme(kBase64Enctype));
  std::string envelope = EnvelopeAround(inside);
  EXPECT_EQ(TimesWritten(envelope, "enctype=\"base64\""), 3U);
  std::string digest;
  EXPECT_TRUE(DecodeProtectBlock(LineAfter(envelope, kDigestBlockLine),
                                 kBase64Enctype, &digest));
  EXPECT_FALSE(digest.empty());
}

// The third of the six fields: the designation of the key the region's data are
// under. The two schemes differ here on purpose -- this tool carries a block as
// the value of one pragma expression and the historical algorithm writes
// characters such a value cannot hold, so a region asking for it gets an
// envelope under this tool's own writing. The designation goes out in that
// writing, the value carried across being the key rather than the characters
// that spelled it. A tool copying the line through would leave the envelope
// declaring one writing and carrying a value in another.
TEST(ProtectEncodingEncryptionOutput, TheDataKeyDesignationIsRewrittenAsWell) {
  std::string envelope = EnvelopeOf(
      RegionDesignatingTheDataKey(kUuencodeEnctype, kDesignationInUuencode));
  std::string named = "enctype=\"";
  named.append(kBlockEnctype).append("\"");
  ASSERT_TRUE(Holds(envelope, named));
  std::string written = LineAfter(envelope, kDataPublicKeyLine);
  EXPECT_NE(written, kDesignationInUuencode);
  std::string key;
  ASSERT_TRUE(DecodeProtectBlock(written, kBlockEnctype, &key));
  EXPECT_EQ(key, kDesignatedKey);
  EXPECT_TRUE(Holds(envelope, TheCountOf(kDesignatedKey.size())));
}

// The fourth: the designation of the key the region's own keys are under. It
// travels the same way and is observed the same way, and it is a separate path
// through the tool -- this one is written beside the key blocks it selects,
// where the one above is written beside the data.
TEST(ProtectEncodingEncryptionOutput, TheKeyDesignationIsRewrittenAsWell) {
  std::string envelope = SealedByDesignation(
      kUuencodeEnctype, kDesignationInUuencode, kDesignatedKey);
  ASSERT_FALSE(Holds(envelope, kSealedDesign));
  std::string written = LineAfter(envelope, kKeyPublicKeyLine);
  EXPECT_NE(written, kDesignationInUuencode);
  std::string key;
  ASSERT_TRUE(DecodeProtectBlock(written, kBlockEnctype, &key));
  EXPECT_EQ(key, kDesignatedKey);
}

// The last two fields, reached one through the other. The block holding the
// region's keys is written under the scheme the envelope declares, so its
// characters give up bytes to that algorithm and those bytes open under the key
// the designation selected; the key that block carries is written under the
// same scheme again, so reading it out leaves the key that opens the data.
//
// Nothing here is taken on trust: the chain ends at the design, which comes out
// of the data block only if all three values along the way were read out of the
// writing the envelope named.
TEST(ProtectEncodingEncryptionOutput, AKeyBlockAndTheKeyInItAreUnderTheScheme) {
  std::string envelope =
      SealedByDesignation(kBase64Enctype, kDesignationInBase64, kDesignatedKey);
  ASSERT_FALSE(Holds(envelope, kSealedDesign));
  ASSERT_TRUE(Holds(envelope, "enctype=\"base64\""));
  std::string block;
  ASSERT_TRUE(DecodeProtectBlock(LineAfter(envelope, kKeyBlockLine),
                                 kBase64Enctype, &block));
  std::string carried;
  ASSERT_TRUE(DecryptProtectedBlock(block, kProviderKey, &carried));
  std::string region_key;
  ASSERT_TRUE(DecodeProtectBlock(LineAfter(carried, kDataDecryptKeyLine),
                                 kBase64Enctype, &region_key));
  std::string design;
  EXPECT_TRUE(DecryptProtectedRegion(DataBlockOf(envelope), region_key, &design,
                                     kBase64Enctype));
  EXPECT_TRUE(Holds(design, kSealedDesign));
}

// The same envelope counted rather than opened. It carries several encoded
// values where the envelopes above carry one or two, and an expression stands
// ahead of every one of them stating that value's own size -- the arrangement a
// text needs to write one field differently from the next. Exactly one
// expression carries no count: the one describing the envelope, not a field.
TEST(ProtectEncodingEncryptionOutput, AnExpressionStandsAheadOfEveryField) {
  std::string envelope =
      SealedByDesignation(kBase64Enctype, kDesignationInBase64, kDesignatedKey);
  size_t expressions = TimesWritten(envelope, kAnyEncoding);
  size_t counts = TimesWritten(envelope, "bytes=");
  EXPECT_GE(counts, 3U);
  EXPECT_EQ(expressions, counts + 1);
}

// A text writing two regions. The rule is about each protected block rather
// than about the first one, so the directive goes into both -- and both designs
// come back from a reading that was told nothing but the key.
//
// The halves are searched separately. A count over the whole text would be met
// by a tool that described one envelope twice and the other not at all.
TEST(ProtectEncodingEncryptionOutput, EachEnvelopeOfATextStatesItsWriting) {
  std::string text = EncryptEnvelopes(TwoRegions(), kExchangeKey);
  EXPECT_FALSE(Holds(text, kSealedDesign));
  EXPECT_FALSE(Holds(text, kSecondDesign));
  size_t first = text.find(kProtectedOpening);
  ASSERT_NE(first, std::string::npos);
  size_t second = text.find(kProtectedOpening, first + 1);
  ASSERT_NE(second, std::string::npos);
  EXPECT_TRUE(Holds(text.substr(first, second - first), kAnyEncoding));
  EXPECT_TRUE(Holds(text.substr(second), kAnyEncoding));
  PreprocFixture f;
  std::string read = Preprocess(text, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, "module sealed_m"));
  EXPECT_TRUE(Holds(read, "module sealed_n"));
}

// What the writing is for: everything an encryption produced comes out as text.
// The design sealed here holds the character that would end the value its block
// travels as and a byte that cannot be printed, and the cipher turns the whole
// of it into arbitrary bytes besides -- and the block is still printable
// characters alone, none of them a quotation mark.
//
// The block is opened as well as inspected: a reading that had found only the
// first few characters -- stopping at a quotation mark inside them -- would
// otherwise report those few as printable and pass.
TEST(ProtectEncodingEncryptionOutput, TheBlockHoldsOnlyWhatASourceLineCarries) {
  std::string region = "`pragma protect begin\n";
  region.append(kAwkwardDesign).append("`pragma protect end\n");
  std::string block = DataBlockOf(EncryptEnvelopes(region, kExchangeKey));
  ASSERT_FALSE(block.empty());
  bool text_only = true;
  for (char c : block) {
    auto byte = static_cast<unsigned char>(c);
    if (byte < 0x21U || byte > 0x7EU || c == '"') text_only = false;
  }
  EXPECT_TRUE(text_only);
  std::string recovered;
  EXPECT_TRUE(DecryptProtectedRegion(block, kExchangeKey, &recovered));
  EXPECT_TRUE(Holds(recovered, kAwkwardDesign));
}

// What the tool states is what the tool did, which is the point of stating it.
// A block written as the value of one pragma expression is a block on one line,
// so there is no length at which its writing was broken and the envelope states
// none -- not even the length the region asked for.
//
// An envelope that repeated the request would send its reader looking for
// breaks that are not there.
TEST(ProtectEncodingEncryptionOutput, AnEnvelopeStatesNoLengthItDidNotBreakAt) {
  std::string envelope =
      EnvelopeAround(StatesEncoding("(enctype=\"base64\", line_length=8)"));
  ASSERT_TRUE(Holds(envelope, "enctype=\"base64\""));
  EXPECT_FALSE(Holds(envelope, "line_length"));
  EXPECT_FALSE(Holds(DataBlockOf(envelope), "\n"));
}

// The length itself, where the writing does break at it: the most characters
// one line may hold once the algorithm has been applied. The descriptor is read
// out of the value a directive writes rather than assembled by hand, so the
// length under test is one a source text really stated. The breaks belong to
// the writing rather than to the data, which is what they are for -- reading
// the text back gives the bytes that went in.
TEST(ProtectEncodingEncryptionOutput, TheStatedLengthBreaksTheWriting) {
  ProtectEncoding stated =
      ParseProtectEncoding("(enctype=\"base64\", line_length=8)");
  ASSERT_EQ(stated.line_length, 8U);
  std::string written = EncodeProtectBlock(kSealedDesign, stated);
  EXPECT_TRUE(Holds(written, "\n"));
  size_t at = 0;
  while (at < written.size()) {
    size_t breaks = written.find('\n', at);
    size_t ends = breaks == std::string::npos ? written.size() : breaks;
    EXPECT_LE(ends - at, 8U);
    at = ends + 1;
  }
  std::string recovered;
  EXPECT_TRUE(DecodeProtectBlock(written, kBase64Enctype, &recovered));
  EXPECT_EQ(recovered, kSealedDesign);
}

// The negative of the length: the one row of the table with nothing for it to
// bound. A length limits the characters a line holds once the writing has been
// applied, and the identity transformation applies none -- the block is the
// data -- so a break put in would be a byte the data never held.
//
// The value is longer than the length asked for, so a scheme that broke at it
// would have broken this, and the descriptor differs from the accepted one
// above in the identifier alone.
TEST(ProtectEncodingEncryptionOutput, TheIdentityTransformationBreaksNoLine) {
  ProtectEncoding stated =
      ParseProtectEncoding("(enctype=\"raw\", line_length=8)");
  ASSERT_EQ(stated.enctype, kRawEnctype);
  ASSERT_EQ(stated.line_length, 8U);
  ASSERT_GT(kSealedDesign.size(), stated.line_length);
  EXPECT_EQ(EncodeProtectBlock(kSealedDesign, stated), kSealedDesign);
}

// ---------------------------------------------------------------------------
// DECRYPTION INPUT: the algorithm and the size a reading takes from it.
// ---------------------------------------------------------------------------

// The whole round trip under a named scheme. The envelope states the writing
// its block was produced by, a reading holding the author's key takes the
// algorithm from that statement, and the design comes back.
TEST(ProtectEncodingDecryptionInput, TheStatedSchemeIsWhatOpensTheBlock) {
  std::string envelope = EnvelopeAround(NamesScheme(kBase64Enctype));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, "module sealed_m"));
}

// The same envelope with another tabulated algorithm declared immediately ahead
// of its block. The identity transformation reads the characters as the data,
// so the reading has bytes in hand and they are not the block's -- the key is
// offered against something the cipher never produced, and the author is told
// rather than left with an empty design.
TEST(ProtectEncodingDecryptionInput, ABlockDeclaredWronglyDoesNotOpen) {
  PreprocFixture f;
  std::string read = Preprocess(EnvelopeReadUnder(NamesScheme(kRawEnctype)), f,
                                HoldingTheKey());
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_FALSE(Holds(read, "module sealed_m"));
}

// The other way a reading can be stopped, and a different thing to be told: an
// identifier standing for no writing at all. There is nothing to measure the
// characters against, so the question of whether they came out of that writing
// cannot even be asked.
//
// The input differs from the one above in the identifier alone.
TEST(ProtectEncodingDecryptionInput, ABlockUnderAnUnprovidedSchemeIsNotRead) {
  std::string declared = NamesScheme(kUnprovidedEnctype);
  PreprocFixture f;
  std::string read =
      Preprocess(EnvelopeReadUnder(declared), f, HoldingTheKey());
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_FALSE(Holds(read, "module sealed_m"));
}

// The same directive as the test above, moved to the other end of the envelope:
// on the line after the word that opens it, with everything the envelope says
// about itself and everything its block says still standing after it. The block
// opens, because what a field is read under is the last expression written
// before that field rather than any expression the envelope holds.
//
// That is what lets a text write one field differently from the next: an
// expression stands ahead of each, and each takes the one nearest above it. The
// pair makes the point -- one directive, two positions, two outcomes -- since a
// tool ignoring the keyword outright would pass here and fail above.
TEST(ProtectEncodingDecryptionInput, AFieldIsReadUnderTheExpressionAboveIt) {
  PreprocFixture f;
  std::string read = Preprocess(EnvelopeOpeningWith(NamesScheme(kRawEnctype)),
                                f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, "module sealed_m"));
}

// A digest block read back under the scheme its envelope declares. The digest
// is a second encoded value, written by a different part of the tool and read
// by a different part of the reading, and it has to come out of the same
// writing as the data block for the check that follows to have anything to
// compare -- so a reading that opens the design and reports nothing has read
// both blocks under the one declared scheme.
TEST(ProtectEncodingDecryptionInput, ADigestBlockIsReadUnderTheSameScheme) {
  std::string inside(kDigestBlockLine);
  inside.append(NamesScheme(kBase64Enctype));
  std::string envelope = EnvelopeAround(inside);
  ASSERT_TRUE(Holds(envelope, kDigestBlockLine));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, "module sealed_m"));
}

// The count an envelope states belongs to the one block written under it.
// §34.5.9.2 defines it as the number of bytes in the original block of data,
// which is a fact about that block and not about the scheme the envelope is
// written in: the scheme stands over everything after it, and the count is
// answered by the value it stands ahead of.
//
// The value inserted here is written in the envelope's own scheme and stands
// after the block with no expression of its own between them, so it is read
// under the very directive the block was read under -- the one carrying the
// block's count. It is a designation of a key rather than a whole sealed
// design, so it is nothing like that count in length, and a reading that held
// the count over would turn it away for its size.
TEST(ProtectEncodingDecryptionInput, TheCountIsSpentOnTheBlockItStandsAheadOf) {
  std::string envelope = EnvelopeAround("");
  size_t block = envelope.find(kBlockOpening);
  ASSERT_NE(block, std::string::npos);
  size_t ends = envelope.find('\n', block);
  ASSERT_NE(ends, std::string::npos);
  std::string written(kDataPublicKeyLine);
  written.append(EncodeProtectBlock(kDesignatedKey, DefaultProtectEncoding()));
  written.append("\n");
  envelope.insert(ends + 1, written);

  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, "module sealed_m"));
}

}  // namespace
