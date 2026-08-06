// §34.5.7 encrypt_agent.
//
// The subclause defines one of the protect pragma keywords §34.4 tabulates,
// and says five things about it.
//
//   Its expression is written with a string against it.
//
//   An encrypting tool draws nothing from the expression: whatever the input
//   wrote against the keyword settles nothing about the encryption now being
//   performed.
//
//   The tool that performs the encryption generates the expression itself and
//   places it in a pragma directive the protected envelope encloses, the
//   string naming that tool.
//
//   The tool keeps the expression it generated out of the data block.
//
//   A decrypting tool draws nothing from the expression either.
//
// All of them are preprocessor-stage rules. The keyword and the directive
// carrying it are in src/preprocessor/protect_keywords.cpp; the name this
// implementation identifies itself by is in
// src/preprocessor/protect_envelope_output.h, and the envelope carrying it is
// written in src/preprocessor/protect_envelope_output.cpp; the half that reads
// an encrypting tool's input, and takes nothing out of it for this keyword, is
// src/preprocessor/protect_processing.cpp; and the reading side, which consumes
// the directive and puts none of it into the design text, is
// src/preprocessor/preprocessor_protect_keys.cpp.
//
// Every input below is written as the real `pragma directive syntax of §22.11,
// with the envelopes of §34.5.1 and §34.5.2 delimiting the regions an
// encrypting tool transforms, the envelopes of §34.5.3 and §34.5.4 delimiting
// the models an earlier encryption already sealed, the entity named by
// §34.5.10's keyword and the key named by §34.5.12's. An envelope that was
// produced was produced because those names really reached a key, and a name
// left inside a previously protected block was left there because §34.5.3's
// own delimiters enclosed it.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity every region below names as having provided the keys its data are
// under, and the name §34.5.12's keyword picks one of that entity's keys out
// with.
constexpr std::string_view kKeyOwner = "acme";
constexpr std::string_view kKeyName = "acme-2026";

// The key that pair reaches: the one every region below is encrypted under.
constexpr std::string_view kRegionKey = "acme-region-exchange-key";

// A name of that entity's that reaches no key at all, for the region there is
// nothing to encrypt.
constexpr std::string_view kUnheldKeyName = "acme-key-nobody-supplied";

// A tool name written in an encrypting tool's input, standing for whatever tool
// the text passed through before this one reached it.
constexpr std::string_view kInputAgent = "AcmeCrypt";

// A second such name, for the model an earlier encryption already sealed.
constexpr std::string_view kOtherAgent = "Globex Sealer 7";

// The design text sealed inside every region below. Nothing of it survives the
// block-alphabet writing of an encrypted block, so finding it in a tool's
// output is finding a region that was never encrypted, and finding it in a
// preprocessor's output is finding one that was opened.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// The two delimiters of a decryption envelope, as an encrypting tool writes
// them and as a text that already holds a protected model writes them.
constexpr std::string_view kBeginProtected =
    "`pragma protect begin_protected\n";
constexpr std::string_view kEndProtected = "`pragma protect end_protected\n";

// Where the expression carrying an envelope's encrypted region begins. What
// follows it, up to the closing quotation mark, is the block itself.
constexpr std::string_view kBlockOpening = "`pragma protect data_block=\"";

// The keyword as it opens a directive of its own, for counting the expressions
// a text holds in the clear without settling what is written against them. The
// '=' keeps the count off the keyword that carries anything further about an
// encrypting tool, that being a different keyword with a longer name.
constexpr std::string_view kAgentDirectiveOpening =
    "`pragma protect encrypt_agent=";

// A user holding the region key of the entity every region names, under the
// key name `held_as`. Written against that entity's own name it is the key the
// regions reach; written against any other it is a key they do not.
ProtectKeyList KeysHeldUnder(std::string_view held_as) {
  ProtectKeyList keys;
  keys.Add(
      {std::string(kKeyOwner), std::string(held_as), std::string(kRegionKey)});
  return keys;
}

// The directives §34.5.10 and §34.5.12 designate that key with. Every region
// below is described by them, so a region that was encrypted was encrypted
// because they reached a key.
std::string NamesTheKey() {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(kKeyOwner).append("\"\n`pragma protect data_keyname=\"");
  text.append(kKeyName).append("\"\n");
  return text;
}

// The expression §34.5.7 defines, carrying `name` as the string it is defined
// with, as a source text reaching an encrypting tool writes it.
std::string NamesAgent(std::string_view name) {
  std::string text = "`pragma protect encrypt_agent=\"";
  text.append(name).append("\"\n");
  return text;
}

// The same expression written in the other position §22.5.1 admits for it: on
// a directive holding a list, beside the expression naming the region's key.
// The entity that provided that key is designated ahead of the list, so a
// region described this way is described as fully as one writing the
// expressions apart.
std::string NamesAgentInAList(std::string_view name) {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(kKeyOwner).append("\"\n`pragma protect encrypt_agent=\"");
  text.append(name).append("\", data_keyname=\"");
  text.append(kKeyName).append("\"\n");
  return text;
}

// The directive an encrypting tool generates for an envelope of its own making:
// the keyword with the name of the tool that performed the encryption written
// against it. That name is this implementation's own, there being no other tool
// the expression could be naming.
std::string GeneratedAgentDirective() {
  std::string text = "`pragma protect encrypt_agent=\"";
  text.append(kEncryptAgent).append("\"\n");
  return text;
}

// One encryption envelope: the delimiters of §34.5.1 and §34.5.2 with
// `described` and then `design` between them.
std::string Region(const std::string& described,
                   std::string_view design = kSealedDesign) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(design);
  text.append("`pragma protect end\n");
  return text;
}

// A model some earlier encryption already sealed, naming the tool that sealed
// it: the delimiters of §34.5.3 and §34.5.4 with that naming between them.
//
// §34.5.1 has such a block travel into a larger envelope as the bytes it is
// written with, so what it encloses is text of the enclosing region rather than
// description of it.
std::string SealedModelNaming(std::string_view name) {
  std::string text(kBeginProtected);
  text.append(NamesAgent(name)).append(kEndProtected);
  return text;
}

// The text that stands where the encryption envelopes of `src` were written,
// for an IP author who supplied the region key under the name `held_as`.
std::string EncryptedUnder(const std::string& src, std::string_view held_as) {
  return EncryptEnvelopes(src, "", KeysHeldUnder(held_as));
}

// The same, for the name the regions below really designate their key by.
std::string Encrypted(const std::string& src) {
  return EncryptedUnder(src, kKeyName);
}

// The text one envelope's block records, recovered with the key the region was
// encrypted under, and empty where the text carries no block or the block does
// not open.
//
// It is the direct reading of what went into a block: a rule about what a block
// shall and shall not hold is settled by opening the block and looking, rather
// than by inference from the characters the block was written as.
std::string OpenedBlockOf(const std::string& envelope) {
  size_t at = envelope.find(kBlockOpening);
  if (at == std::string::npos) return {};
  size_t start = at + kBlockOpening.size();
  size_t end = envelope.find('"', start);
  if (end == std::string::npos) return {};
  std::string cleartext;
  if (!DecryptProtectedRegion(envelope.substr(start, end - start), kRegionKey,
                              &cleartext)) {
    return {};
  }
  return cleartext;
}

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

// A reading of `src` by a tool holding the key every region below is under,
// with the diagnostics that reading raised.
struct ReadingUnderTheKey {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit ReadingUnderTheKey(const std::string& src) {
    PreprocConfig config;
    config.protect_keys = KeysHeldUnder(kKeyName);
    Preprocessor pp(mgr, diag, config);
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

// ---------------------------------------------------------------------------
// An encrypting tool draws nothing from the expression in its input.
// ---------------------------------------------------------------------------

// A region naming a tool of its own is encrypted by this one, and the envelope
// taking that region's place names this one. The name the region wrote reaches
// none of the text standing in the clear: it named whatever tool the text
// passed through before, and that is not the tool that performed this
// encryption.
TEST(ProtectEncryptAgentEncryptionInput, TheToolWritesItsOwnNameOverTheInputs) {
  std::string described = NamesTheKey() + NamesAgent(kInputAgent);
  std::string encrypted = Encrypted(Region(described));
  EXPECT_EQ(Occurrences(encrypted, kAgentDirectiveOpening), 1U);
  EXPECT_NE(encrypted.find(GeneratedAgentDirective()), std::string::npos);
  EXPECT_EQ(encrypted.find(NamesAgent(kInputAgent)), std::string::npos);
}

// Where the region's own expression went instead, read directly: the block is
// opened with the key the region was encrypted under and the expression is
// inside it, whole. Nothing holds it back from there, because there is nothing
// the encryption takes out of it.
TEST(ProtectEncryptAgentEncryptionInput, AnExpressionInTheRegionIsSealed) {
  std::string described = NamesTheKey() + NamesAgent(kInputAgent);
  std::string opened = OpenedBlockOf(Encrypted(Region(described)));
  EXPECT_NE(opened.find(kSealedDesign), std::string::npos);
  EXPECT_NE(opened.find(NamesAgent(kInputAgent)), std::string::npos);
}

// §34.5.9 has an encrypting tool state how much data a block stands for, so the
// count is what the envelope itself says about the size of the text it sealed.
// The count covers the region's own expression, that expression being text of
// the region like any other rather than something lifted out of it.
TEST(ProtectEncryptAgentEncryptionInput, TheStatedBlockSizeCountsTheLine) {
  std::string described = NamesTheKey() + NamesAgent(kInputAgent);
  std::string sealed = described + std::string(kSealedDesign);
  std::string bytes = "bytes=";
  bytes.append(std::to_string(ProtectedRegionBlockSize(sealed))).append(")");
  EXPECT_NE(Encrypted(Region(described)).find(bytes), std::string::npos);
}

// The negative of the syntax: the keyword standing alone, with no string
// against it. That is not the expression the subclause defines, and it settles
// no more about the encryption than the defined spelling does, so it too is
// sealed along with the design.
TEST(ProtectEncryptAgentEncryptionInput, TheKeywordStandingAloneIsSealedToo) {
  std::string described = NamesTheKey() + "`pragma protect encrypt_agent\n";
  std::string encrypted = Encrypted(Region(described));
  EXPECT_EQ(Occurrences(encrypted, kAgentDirectiveOpening), 1U);
  EXPECT_NE(OpenedBlockOf(encrypted).find("`pragma protect encrypt_agent\n"),
            std::string::npos);
}

// §22.5.1 gives a pragma_value more than one spelling, and none of them is a
// spelling this tool takes a name from. A name written as a bare identifier is
// sealed where it stands, exactly as the quoted spelling is.
TEST(ProtectEncryptAgentEncryptionInput, AnIdentifierValueIsSealedToo) {
  std::string described =
      NamesTheKey() + "`pragma protect encrypt_agent=acme_crypt\n";
  std::string encrypted = Encrypted(Region(described));
  EXPECT_NE(encrypted.find(GeneratedAgentDirective()), std::string::npos);
  EXPECT_NE(OpenedBlockOf(encrypted).find("encrypt_agent=acme_crypt"),
            std::string::npos);
}

// The third spelling §22.5.1 admits, for the reason the second is sealed: a
// number written against the keyword names the tool that performed this
// encryption no better than a name written against it does, so it too stays
// where the region wrote it.
TEST(ProtectEncryptAgentEncryptionInput, ANumberValueIsSealedToo) {
  std::string described =
      NamesTheKey() + "`pragma protect encrypt_agent=1998\n";
  std::string encrypted = Encrypted(Region(described));
  EXPECT_NE(encrypted.find(GeneratedAgentDirective()), std::string::npos);
  EXPECT_NE(OpenedBlockOf(encrypted).find("encrypt_agent=1998"),
            std::string::npos);
}

// The expression written on a directive holding a list is the same expression,
// and is passed over the same way. The region here designates its key on that
// very directive and was still encrypted, so the list was read whole rather
// than abandoned at the expression this subclause defines.
TEST(ProtectEncryptAgentEncryptionInput, AnExpressionInAListIsPassedToo) {
  std::string encrypted = Encrypted(Region(NamesAgentInAList(kInputAgent)));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find(GeneratedAgentDirective()), std::string::npos);
}

// A text with no encryption envelope in it holds the expression where it was
// written, character for character, spacing and all. The transformation takes
// nothing from it and there is no envelope for it to be placed inside, so it
// is neither read nor rewritten.
TEST(ProtectEncryptAgentEncryptionInput, AnExpressionOutsideEnvelopesStays) {
  std::string src = "module m;\n";
  src.append("`pragma  protect   encrypt_agent  =  \"AcmeCrypt\"\n");
  src.append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

// §34.4 makes the scope of a protect pragma keyword lexical, so an expression
// written ahead of an envelope is in effect inside it. That is still not a
// place the encryption takes anything from: the expression stays outside the
// envelope, on the line it was written on, and is written exactly once.
TEST(ProtectEncryptAgentEncryptionInput, AnExpressionAheadOfTheEnvelopeStays) {
  std::string encrypted =
      Encrypted(NamesAgent(kInputAgent) + Region(NamesTheKey()));
  EXPECT_EQ(Occurrences(encrypted, NamesAgent(kInputAgent)), 1U);
  EXPECT_LT(encrypted.find(NamesAgent(kInputAgent)),
            encrypted.find(kBeginProtected));
}

// A name one region wrote reaches the envelope after it by that same lexical
// scope. It describes that envelope no better than it described its own, so
// each of the two envelopes carries an expression the tool generated for it and
// neither carries the name the first region held.
//
// Two envelopes are what the text is built from, because an envelope leaning on
// a name placed in the envelope before it would say nothing about the tool that
// sealed it wherever the two came to be separated. The count of opening
// delimiters is what says two envelopes were really produced.
TEST(ProtectEncryptAgentEncryptionInput, ANameFromAnEarlierRegionIsNotUsed) {
  std::string first = Region(NamesTheKey() + NamesAgent(kInputAgent));
  std::string second = Region(NamesTheKey(), "module second_m; endmodule\n");
  std::string encrypted = Encrypted(first + second);
  EXPECT_EQ(Occurrences(encrypted, kBeginProtected), 2U);
  EXPECT_EQ(Occurrences(encrypted, GeneratedAgentDirective()), 2U);
  EXPECT_EQ(Occurrences(encrypted, kAgentDirectiveOpening), 2U);
}

// ---------------------------------------------------------------------------
// The tool generates the expression and names itself with it.
// ---------------------------------------------------------------------------

// A region that says nothing at all about an encrypting tool is still described
// by one: the expression is generated for the envelope rather than carried over
// from the text the envelope was made from.
TEST(ProtectEncryptAgentEncryptionOutput, TheToolGeneratesTheExpressionItself) {
  std::string encrypted = Encrypted(Region(NamesTheKey()));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(Occurrences(encrypted, GeneratedAgentDirective()), 1U);
}

// What describes an envelope is the name the tool generated, not the name
// standing in effect over the place the envelope was written. The expression
// reaching in from ahead of it named a tool that did not perform this
// encryption, so nothing inside the envelope carries that name.
TEST(ProtectEncryptAgentEncryptionOutput, AnEnvelopeIsDescribedByItsMaker) {
  std::string encrypted =
      Encrypted(NamesAgent(kInputAgent) + Region(NamesTheKey()));
  size_t envelope = encrypted.find(kBeginProtected);
  EXPECT_LT(envelope, encrypted.find(GeneratedAgentDirective()));
  EXPECT_EQ(encrypted.find(NamesAgent(kInputAgent), envelope),
            std::string::npos);
}

// The string is written against the keyword, which is the spelling §34.5.7.1
// defines the expression with, and it names a tool rather than standing empty.
// The keyword written alone would name nothing, and an envelope stating no name
// would leave a reader unable to tell which tool sealed it.
TEST(ProtectEncryptAgentEncryptionOutput, TheStringAgainstTheKeywordNamesIt) {
  std::string encrypted = Encrypted(Region(NamesTheKey()));
  EXPECT_FALSE(kEncryptAgent.empty());
  EXPECT_NE(encrypted.find(GeneratedAgentDirective()), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect encrypt_agent\n"),
            std::string::npos);
}

// The directive stands between the two expressions delimiting the envelope, so
// a reader that has reached the envelope has reached the name of the tool that
// made it.
TEST(ProtectEncryptAgentEncryptionOutput, TheDirectiveStandsInsideTheEnvelope) {
  std::string encrypted = Encrypted(Region(NamesTheKey()));
  EXPECT_LT(encrypted.find(kBeginProtected),
            encrypted.find(GeneratedAgentDirective()));
  EXPECT_LT(encrypted.find(GeneratedAgentDirective()),
            encrypted.find(kEndProtected));
}

// The name is readable without a key, which is what placing it in a directive
// rather than in the block is for. It stands ahead of the block, so nothing a
// reader has to open comes between the envelope and the name of the tool that
// wrote it.
TEST(ProtectEncryptAgentEncryptionOutput, TheDirectiveStandsAheadOfTheBlock) {
  std::string encrypted = Encrypted(Region(NamesTheKey()));
  EXPECT_NE(encrypted.find(kBlockOpening), std::string::npos);
  EXPECT_LT(encrypted.find(GeneratedAgentDirective()),
            encrypted.find(kBlockOpening));
}

// The negative of generating one: a region there is no key to encrypt is not
// transformed into an envelope at all, so there is no envelope for an
// expression to be enclosed by and none is written. The key held here is held
// under a name this region designates nothing by, which is what leaves the
// region untransformed.
TEST(ProtectEncryptAgentEncryptionOutput, ARegionWithNoKeyGetsNoExpression) {
  std::string src = Region(NamesTheKey() + NamesAgent(kInputAgent));
  EXPECT_EQ(EncryptedUnder(src, kUnheldKeyName), src);
}

// ---------------------------------------------------------------------------
// The generated expression is not encrypted into the data block.
// ---------------------------------------------------------------------------

// The block is opened with the key the region was encrypted under and read
// whole: what it records is the region's own text and nothing besides. The
// generated expression was added to the envelope rather than to the text the
// block was written from, so the two are the same text character for character
// -- which says the expression was kept out of the block rather than merely
// written outside it as well.
//
// The rule is observed by opening the block and comparing, rather than by
// inference from the characters the block was written as.
TEST(ProtectEncryptAgentEncryptionOutput, TheBlockIsTheOneTheRegionsTextGives) {
  std::string described = NamesTheKey();
  std::string encrypted = Encrypted(Region(described));
  EXPECT_NE(encrypted.find(kBlockOpening), std::string::npos);
  EXPECT_EQ(OpenedBlockOf(encrypted), described + std::string(kSealedDesign));
}

// A name a previously protected model wrote inside itself is not this
// envelope's. §34.5.3 leaves the expressions of such a block uninterpreted and
// §34.5.1 has the block travel into the larger envelope as the bytes it is
// written with, so the generated expression stands alone in the clear and names
// the tool that sealed the larger model.
TEST(ProtectEncryptAgentEncryptionOutput, ASealedModelsNameDisplacesNothing) {
  std::string described = NamesTheKey() + SealedModelNaming(kOtherAgent);
  std::string encrypted = Encrypted(Region(described));
  EXPECT_EQ(Occurrences(encrypted, kAgentDirectiveOpening), 1U);
  EXPECT_NE(encrypted.find(GeneratedAgentDirective()), std::string::npos);
}

// The same name, shown to have gone into the block rather than to have been
// dropped: opening the block finds the sealed model whole, its own naming
// included.
TEST(ProtectEncryptAgentEncryptionOutput, ASealedModelsNameIsSealedWithIt) {
  std::string described = NamesTheKey() + SealedModelNaming(kOtherAgent);
  std::string opened = OpenedBlockOf(Encrypted(Region(described)));
  EXPECT_NE(opened.find(NamesAgent(kOtherAgent)), std::string::npos);
}

// ---------------------------------------------------------------------------
// A decrypting tool draws nothing from the expression.
// ---------------------------------------------------------------------------

// The whole round trip: a region comes back as the design it was written from,
// and the name of the tool that sealed it reaches none of the text the
// compilation step after the preprocessor reads. The expression describes the
// envelope rather than the design, so nothing of it is design text.
TEST(ProtectEncryptAgentDecryptionInput, TheNameReachesNoneOfTheDesignText) {
  ReadingUnderTheKey read(Encrypted(Region(NamesTheKey())));
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kEncryptAgent));
}

// The reading takes nothing from it and objects to nothing about it either. An
// envelope naming the tool that sealed it is read as far as its design text
// goes, so the name costs the reading neither a diagnostic nor the block.
TEST(ProtectEncryptAgentDecryptionInput, TheNameCostsTheReadingNothing) {
  ReadingUnderTheKey read(Encrypted(Region(NamesTheKey())));
  EXPECT_FALSE(read.diag.HasErrors());
}

// The same round trip, built from a model an earlier encryption had already
// sealed. That model's own naming travelled into this envelope's block as the
// bytes it was written with, came back out when the block was opened, and was
// read there as the description it is: none of it is design text either.
TEST(ProtectEncryptAgentDecryptionInput, ASealedModelsNameReachesNoDesignText) {
  std::string described = NamesTheKey() + SealedModelNaming(kOtherAgent);
  ReadingUnderTheKey read(Encrypted(Region(described)));
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kOtherAgent));
}

// The same of an envelope this tool did not produce, which names some other
// tool as the one that sealed it and stands in whatever order its producer
// wrote it. What tool sealed an envelope is not something the reading draws on,
// so a foreign name is read past and reaches none of the design text.
TEST(ProtectEncryptAgentDecryptionInput, AForeignEnvelopeNamingAnAgentIsRead) {
  std::string envelope(kBeginProtected);
  envelope.append(NamesAgent(kInputAgent)).append(kEndProtected);
  ReadingUnderTheKey read(envelope);
  EXPECT_FALSE(read.Holds(kInputAgent));
}

}  // namespace
