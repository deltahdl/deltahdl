// §34.5.5 author.
//
// The subclause defines one of the protect pragma keywords §34.4 tabulates,
// and says five things about it.
//
//   Its expression is written with a string against it.
//
//   Found in an encrypting tool's input, that string identifies by name
//   whoever wrote the IP the envelope carries.
//
//   It is a keyword of its own rather than one spelling of the keyword
//   carrying uninterpreted documentation, so the author is found without
//   reading a documentation string for one.
//
//   An encrypting tool that finds the expression in an encryption envelope
//   places it in a pragma directive the protected envelope encloses, and keeps
//   it out of the data block. An expression the encryption envelope does not
//   hold is copied into the output stream without change.
//
//   A decrypting tool draws nothing from it.
//
// All of them are preprocessor-stage rules. The keyword and the directive
// carrying it are in src/preprocessor/protect_keywords.cpp; the half that reads
// an encrypting tool's input for the expression and holds it back from the text
// a block records is src/preprocessor/protect_processing.cpp; the half that
// writes it inside the envelope taking that region's place is
// src/preprocessor/protect_envelope_output.cpp; and the reading side, which
// consumes the directive and puts none of it into the design text, is
// src/preprocessor/preprocessor.cpp.
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
#include "helpers_protect_region.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The string a region names its author with, and the directive text that names
// them. The name is written with a space in it so that it can only have arrived
// in the output as the value of an expression rather than as a stray word.
constexpr std::string_view kAuthorName = "Ada Lovelace";
constexpr std::string_view kAuthorDirective =
    "`pragma protect author=\"Ada Lovelace\"\n";

// A second name, for the inputs that write the expression twice or write one
// region against another.
constexpr std::string_view kOtherAuthorName = "Grace Hopper";

// The expression §34.5.5 defines, carrying `name` as the string it is defined
// with.
//
// It serves both sides. A source text names its author by writing this, and an
// encrypting tool placing the expression inside the envelope writes the same
// thing, so the text a tool produced is compared against the spelling an input
// is built from.
std::string NamesAuthor(std::string_view name) {
  std::string text = "`pragma protect author=\"";
  text.append(name).append("\"\n");
  return text;
}

// The same expression written in the other position §22.5.1 admits for it: on a
// directive holding a list, beside the expression naming the region's key. The
// author expression is the same one either way, so what §34.5.5 says of it
// holds wherever the directive carrying it was written.
std::string NamesAuthorBesideKeyName(std::string_view name) {
  std::string text = "`pragma protect author=\"";
  text.append(name).append("\", data_keyname=\"");
  text.append(kKeyName).append("\"\n");
  return text;
}

// A model some earlier encryption already sealed: the delimiters of §34.5.3 and
// §34.5.4 with `enclosed` between them.
//
// §34.5.1 has such a block travel into a larger envelope as the bytes it is
// written with, so what it encloses is text of the enclosing region rather than
// description of it.
std::string PreviouslyProtected(const std::string& enclosed) {
  std::string text(kBeginProtected);
  text.append(enclosed);
  text.append(kEndProtected);
  return text;
}

// The text that stands where the encryption envelopes of `src` were written,
// for an IP author who supplied keys under the names that select them.
std::string EncryptedUnder(const std::string& src, const ProtectKeyList& keys) {
  return EncryptEnvelopes(src, "", keys);
}

// A reading of `src` by a tool holding the keys every region below is under,
// with the diagnostics that reading raised.
struct ReadUnderRegionKeys {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit ReadUnderRegionKeys(const std::string& src) {
    PreprocConfig config;
    config.protect_keys = TheRegionsKey();
    Preprocessor pp(mgr, diag, config);
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

// ---------------------------------------------------------------------------
// The string names the author, and it is a keyword of its own.
// ---------------------------------------------------------------------------

// The name a region wrote against the keyword is the name the envelope taking
// that region's place carries. Nothing else in this input holds those
// characters, so a name standing in the output arrived there as the value of
// this expression.
TEST(ProtectAuthorEncryptionInput, TheStringAgainstTheKeywordNamesTheAuthor) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find(kAuthorDirective), std::string::npos);
}

// The negative of the syntax: the keyword standing alone, with no string
// against it. That is not the expression the subclause defines, so it names
// nobody and the envelope has no author to state.
TEST(ProtectAuthorEncryptionInput, TheKeywordStandingAloneNamesNobody) {
  std::string enclosed = ReachesTheKey();
  enclosed.append("`pragma protect author\n").append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find(kBeginProtected), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect author"), std::string::npos);
}

// The keyword carrying uninterpreted documentation is a different keyword, so
// the same string written against it names no author. A tool looking for the
// author of this envelope finds none rather than finding one by reading a
// documentation string for it.
TEST(ProtectAuthorEncryptionInput, ADocumentationStringNamesNoAuthor) {
  std::string enclosed = ReachesTheKey();
  enclosed.append("`pragma protect comment=\"Ada Lovelace\"\n");
  enclosed.append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find(kBeginProtected), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect author"), std::string::npos);
}

// The two stand apart where a region writes both: the author's name is the one
// written against this keyword, and the documentation written beside it says
// nothing about who the author is.
TEST(ProtectAuthorEncryptionInput, TheAuthorIsTakenApartFromTheDocumentation) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName));
  enclosed.append("`pragma protect comment=\"Grace Hopper\"\n");
  enclosed.append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find(kAuthorDirective), std::string::npos);
  EXPECT_EQ(encrypted.find(NamesAuthor(kOtherAuthorName)), std::string::npos);
}

// ---------------------------------------------------------------------------
// The expression is placed in a directive the protected envelope encloses.
// ---------------------------------------------------------------------------

// The directive stands between the two expressions delimiting the envelope, so
// a reader that has reached the envelope has reached the name inside it. It is
// written once: the expression the source wrote was held back from the block
// rather than written out beside a copy of itself.
TEST(ProtectAuthorEncryptionOutput, TheDirectiveStandsInsideTheEnvelope) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_EQ(TimesWritten(encrypted, kAuthorDirective), 1U);
  EXPECT_LT(encrypted.find(kBeginProtected), encrypted.find(kAuthorDirective));
  EXPECT_LT(encrypted.find(kAuthorDirective), encrypted.find(kEndProtected));
}

// The name is readable without a key, which is what placing it in a directive
// rather than in the block is for. It stands ahead of the block, so nothing a
// reader has to open comes between the envelope and the name of its author.
TEST(ProtectAuthorEncryptionOutput, TheDirectiveStandsAheadOfTheBlock) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find(kBlockOpening), std::string::npos);
  EXPECT_LT(encrypted.find(kAuthorDirective), encrypted.find(kBlockOpening));
}

// The negative: a region whose text names no author has no expression to place,
// so the envelope carries no such directive. What is written is the expression
// the region held rather than the keyword as a matter of course.
TEST(ProtectAuthorEncryptionOutput, ARegionNamingNoAuthorWritesNoDirective) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find(kBeginProtected), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect author"), std::string::npos);
}

// §22.5.1 gives a pragma_value more than one spelling, and what is placed in
// the directive is the expression the source wrote. A name written as a bare
// identifier therefore goes out as that identifier: returned in quotes it would
// be a different pragma_value from the one placed there.
TEST(ProtectAuthorEncryptionOutput, AnIdentifierValueIsPlacedAsItWasWritten) {
  std::string enclosed = ReachesTheKey();
  enclosed.append("`pragma protect author=ada_lovelace\n");
  enclosed.append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find("`pragma protect author=ada_lovelace\n"),
            std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect author=\"ada_lovelace\""),
            std::string::npos);
}

// The third spelling §22.5.1 admits, for the same reason: a number written
// against the keyword is placed as the number the source wrote.
TEST(ProtectAuthorEncryptionOutput, ANumberValueIsPlacedAsItWasWritten) {
  std::string enclosed = ReachesTheKey();
  enclosed.append("`pragma protect author=1843\n").append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find("`pragma protect author=1843\n"), std::string::npos);
}

// The expression written on a directive holding a list is the same expression,
// so it is placed the same way. The region here names its key on that very
// directive and was still encrypted, so the list was read whole rather than
// abandoned at the author's expression.
TEST(ProtectAuthorEncryptionOutput, AnExpressionSharingADirectiveIsPlaced) {
  std::string enclosed = DesignatesTheProvider();
  enclosed.append(NamesAuthorBesideKeyName(kAuthorName));
  enclosed.append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find(kAuthorDirective), std::string::npos);
}

// A region naming an author twice named one author: the scope of a protect
// pragma keyword is lexical, so what stands in effect where the region ends is
// the most recent writing of it, and that is the one expression the envelope
// carries.
TEST(ProtectAuthorEncryptionOutput, TheLatestNamingInTheRegionIsTheOnePlaced) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName));
  enclosed.append(NamesAuthor(kOtherAuthorName)).append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_EQ(TimesWritten(encrypted, NamesAuthor(kOtherAuthorName)), 1U);
  EXPECT_EQ(encrypted.find(kAuthorDirective), std::string::npos);
}

// Each envelope carries the author its own region named. Two envelopes are read
// on their own by whatever reaches them, so one relying on a name placed in the
// envelope before it would say nothing about its author wherever the two are
// separated.
TEST(ProtectAuthorEncryptionOutput, EachEnvelopeCarriesItsOwnRegionsAuthor) {
  std::string first = ReachesTheKey();
  first.append(NamesAuthor(kAuthorName)).append("module first_m; endmodule\n");
  std::string second = ReachesTheKey();
  second.append(NamesAuthor(kOtherAuthorName));
  second.append("module second_m; endmodule\n");
  std::string encrypted = Encrypted(RegionAround(first) + RegionAround(second));
  EXPECT_EQ(TimesWritten(encrypted, kBeginProtected), 2U);
  EXPECT_EQ(TimesWritten(encrypted, kAuthorDirective), 1U);
  EXPECT_EQ(TimesWritten(encrypted, NamesAuthor(kOtherAuthorName)), 1U);
}

// ---------------------------------------------------------------------------
// The expression is not encrypted into the data block.
// ---------------------------------------------------------------------------

// The block is opened with the key the region was encrypted under and read: the
// design the region held is there, and the expression naming its author is not.
// This is the rule observed directly rather than inferred from the characters
// the block was written as.
TEST(ProtectAuthorEncryptionOutput, TheOpenedBlockHoldsNoNaming) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  std::string opened = OpenedBlockOf(Encrypted(RegionAround(enclosed)));
  EXPECT_NE(opened.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(opened.find("`pragma protect author"), std::string::npos);
}

// The same of the expression written on a directive holding a list: what is
// kept out of the block is the author's name, wherever the directive carrying
// it stood.
TEST(ProtectAuthorEncryptionOutput, ASharedDirectivesNamingIsKeptOut) {
  std::string enclosed = DesignatesTheProvider();
  enclosed.append(NamesAuthorBesideKeyName(kAuthorName));
  enclosed.append(kSealedDesign);
  std::string opened = OpenedBlockOf(Encrypted(RegionAround(enclosed)));
  EXPECT_NE(opened.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(opened.find(kAuthorName), std::string::npos);
}

// The negative of the same rule, and the other half of the keyword standing
// alone: naming nobody, it is not the expression this subclause holds back, so
// §34.5.1's rule for the rest of the enclosed text governs and it goes into the
// block along with the design.
TEST(ProtectAuthorEncryptionOutput, TheKeywordStandingAloneIsEncrypted) {
  std::string enclosed = ReachesTheKey();
  enclosed.append("`pragma protect author\n").append(kSealedDesign);
  std::string opened = OpenedBlockOf(Encrypted(RegionAround(enclosed)));
  EXPECT_NE(opened.find("`pragma protect author\n"), std::string::npos);
}

// The block a region naming its author is written into is the block written
// from the same region with the naming struck out. The cipher is a function of
// the text and the key, so two blocks written alike were written from the same
// text.
TEST(ProtectAuthorEncryptionOutput, TheBlockIsTheOneWrittenWithoutTheNaming) {
  std::string named = ReachesTheKey();
  named.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  std::string unnamed = ReachesTheKey();
  unnamed.append(kSealedDesign);
  std::string with_author = Encrypted(RegionAround(named));
  std::string without = Encrypted(RegionAround(unnamed));
  EXPECT_FALSE(DataBlockOf(without).empty());
  EXPECT_EQ(DataBlockOf(with_author), DataBlockOf(without));
}

// §34.5.9 has an encrypting tool state how much data a block stands for, so the
// count is what the envelope itself says about the size of the text it sealed.
// The count is the same either way, an envelope naming its author having sealed
// exactly the text an envelope naming none sealed.
TEST(ProtectAuthorEncryptionOutput, TheStatedBlockSizeExcludesTheNaming) {
  std::string named = ReachesTheKey();
  named.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  std::string unnamed = ReachesTheKey();
  unnamed.append(kSealedDesign);
  std::string bytes = "bytes=";
  bytes.append(std::to_string(ProtectedRegionBlockSize(unnamed))).append(")");
  EXPECT_NE(Encrypted(RegionAround(named)).find(bytes), std::string::npos);
}

// The negative, built from the block §34.5.3 and §34.5.4 delimit: an expression
// a previously protected model wrote inside itself is not this envelope's
// author. §34.5.1 has that model travel into the larger envelope as the bytes
// it is written with, so the naming stays where it was written -- inside the
// block -- and the envelope places no directive of its own.
TEST(ProtectAuthorEncryptionOutput, ANamingInsideASealedModelIsNotPlaced) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(PreviouslyProtected(NamesAuthor(kAuthorName)));
  enclosed.append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find(kBeginProtected), std::string::npos);
  EXPECT_EQ(encrypted.find(kAuthorDirective), std::string::npos);
}

// The same naming, shown to have gone into the block rather than to have been
// dropped: opening the block finds the sealed model whole, its own naming
// included.
TEST(ProtectAuthorEncryptionOutput, ANamingInsideASealedModelIsEncrypted) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(PreviouslyProtected(NamesAuthor(kAuthorName)));
  enclosed.append(kSealedDesign);
  std::string opened = OpenedBlockOf(Encrypted(RegionAround(enclosed)));
  EXPECT_NE(opened.find(kAuthorDirective), std::string::npos);
}

// ---------------------------------------------------------------------------
// An expression the encryption envelope does not hold is copied unchanged.
// ---------------------------------------------------------------------------

// A text with no encryption envelope in it holds the expression where it was
// written, character for character, spacing and all. There is no envelope for
// it to be placed inside, and it is not something the transformation rewrites.
TEST(ProtectAuthorEncryptionOutput, AnExpressionOutsideEveryEnvelopeIsCopied) {
  std::string src = "module m;\n";
  src.append("`pragma  protect   author  =  \"Ada Lovelace\"\n");
  src.append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

// An expression written ahead of an envelope is copied where it stands rather
// than lifted into that envelope. §34.5.5 asks for the expression the
// encryption envelope holds, and this one is outside it, so it is written once
// and the envelope carries no directive of its own.
TEST(ProtectAuthorEncryptionOutput, AnExpressionAheadOfTheEnvelopeIsCopied) {
  std::string src = NamesAuthor(kAuthorName);
  std::string enclosed = ReachesTheKey();
  enclosed.append(kSealedDesign);
  src.append(RegionAround(enclosed));
  std::string encrypted = Encrypted(src);
  EXPECT_EQ(TimesWritten(encrypted, kAuthorDirective), 1U);
  EXPECT_LT(encrypted.find(kAuthorDirective), encrypted.find(kBeginProtected));
}

// The same for one written after the envelope: it stands behind the envelope in
// the output as it stood behind it in the input.
TEST(ProtectAuthorEncryptionOutput, AnExpressionAfterTheEnvelopeIsCopied) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(kSealedDesign);
  std::string src = RegionAround(enclosed) + NamesAuthor(kAuthorName);
  std::string encrypted = Encrypted(src);
  EXPECT_EQ(TimesWritten(encrypted, kAuthorDirective), 1U);
  EXPECT_LT(encrypted.find(kEndProtected), encrypted.find(kAuthorDirective));
}

// A region there is nothing to encrypt is not transformed at all, so the naming
// inside it is text of the source like everything else there and goes back
// exactly as it was written. The keys held here reach no key of this region's,
// which is what leaves the region untransformed.
TEST(ProtectAuthorEncryptionOutput, ARegionWithNoKeyKeepsItsNamingAsWritten) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  std::string src = RegionAround(enclosed);
  EXPECT_EQ(EncryptedUnder(src, AKeyUnderAnotherName()), src);
}

// ---------------------------------------------------------------------------
// A decrypting tool draws nothing from the expression.
// ---------------------------------------------------------------------------

// The whole round trip: a region naming its author comes back as the design it
// was written from, and the name reaches none of the text the compilation step
// after the preprocessor reads. The expression describes the envelope rather
// than the design, so nothing of it is design text.
TEST(ProtectAuthorDecryptionInput, TheNameReachesNoneOfTheDesignText) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  ReadUnderRegionKeys read(Encrypted(RegionAround(enclosed)));
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kAuthorName));
}

// The reading takes nothing from it and objects to nothing about it either. An
// envelope naming its author is read exactly as far as one naming none is, so
// the name costs the reading neither a diagnostic nor the block.
TEST(ProtectAuthorDecryptionInput, TheNameCostsTheReadingNothing) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  ReadUnderRegionKeys read(Encrypted(RegionAround(enclosed)));
  EXPECT_FALSE(read.diag.HasErrors());
}

// The same of an envelope this tool did not produce, whose directives stand in
// whatever order its producer wrote them. What order another producer wrote its
// expressions in is not something a reader gets to settle, and a name written
// among them is still nothing the reading draws on.
TEST(ProtectAuthorDecryptionInput, AForeignEnvelopeNamingAnAuthorIsRead) {
  std::string envelope(kBeginProtected);
  envelope.append(NamesAuthor(kAuthorName)).append(kEndProtected);
  ReadUnderRegionKeys read(envelope);
  EXPECT_FALSE(read.Holds(kAuthorName));
}

}  // namespace
