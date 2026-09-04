#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_protect_region.h"
#include "helpers_protect_viewport.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"
#include "preprocessor/protect_viewport.h"

using namespace delta;

// Exercises what §34.5.31.2 has the reset expression do.
//
// ENCRYPTION INPUT states it by naming something that already does it: the
// expression is a synonym for a reset pragma directive containing protect in
// its pragma keyword list, and following the reset every protect pragma keyword
// stands at its default. The subclause gives the reason a text writes one --
// §34.4 runs a keyword's scope to the end of the compilation input, so an
// author who states common keywords ahead of a list of files states them over
// whatever is compiled after that list until something puts them back.
//
// ENCRYPTION OUTPUT is none, so an envelope produced from a text that wrote a
// reset carries no reset expression on that account. DECRYPTION INPUT is none
// as well: the expression opens no envelope and closes none, and what a reading
// does with it is what §34.4 does with the directive it is a synonym for.

namespace {

// The entity a text names for the keys its data are under, a key of that
// entity, the algorithm §34.5.21 has it name for computing its digests and the
// cipher §34.5.24 has it name for encrypting its own keys. Four keywords from
// four subclauses are written together so that a reading which put one family
// back and left another standing is told apart from one that put back all four.
constexpr std::string_view kProvider = "Meridian Aerospace";
constexpr std::string_view kProvidersKey = "meridian-2031";
constexpr std::string_view kDigestAlgorithm = "sha256";
constexpr std::string_view kKeyCipher = "rsa";

// The two of those four tabulated names this file has to spell for itself,
// protect_keywords.h naming the other two.
constexpr std::string_view kDigestMethodKeyword = "digest_method";
constexpr std::string_view kKeyMethodKeyword = "key_method";

// The entity a text names second, for the case writing a name after the reset.
constexpr std::string_view kSecondProvider = "Vantage Optics";

// The expression §34.5.31.1 defines, written on a directive of its own.
std::string Restores() { return "`pragma protect reset\n"; }

// The directive §22.11.1 defines with protect in its pragma keyword list, which
// §34.5.31.2 says the expression above is a synonym for.
std::string ResetPragma() { return "`pragma reset protect\n"; }

// The expression itself, without the line it is written on, for counting how
// many of them the cleartext of a produced envelope carries.
constexpr std::string_view kResetExpression = "`pragma protect reset";

// A directive writing `value` against `keyword`.
std::string Writes(std::string_view keyword, std::string_view value) {
  std::string written = "`pragma protect ";
  written.append(keyword).append("=\"").append(value).append("\"\n");
  return written;
}

// The four keywords, each written against the value this file reads back.
std::string StatesFour() {
  std::string written = Writes(kDataKeyownerKeyword, kProvider);
  written.append(Writes(kDataKeynameKeyword, kProvidersKey));
  written.append(Writes(kDigestMethodKeyword, kDigestAlgorithm));
  written.append(Writes(kKeyMethodKeyword, kKeyCipher));
  return written;
}

// Whether a reading has all four of those keywords back at their defaults.
bool AllFourAreBack(const ReadKeywordScope& scope) {
  return scope.ValueOf(kDataKeyownerKeyword).defaulted &&
         scope.ValueOf(kDataKeynameKeyword).defaulted &&
         scope.ValueOf(kDigestMethodKeyword).defaulted &&
         scope.ValueOf(kKeyMethodKeyword).defaulted;
}

// §34.5.31.2: following the reset, all protect pragma keywords are restored to
// their default values. Four families are written and four are asked about, a
// reset that reached only the family it was written beside being the thing one
// keyword could not tell apart.
TEST(ProtectResetDescription, EveryKeywordTheTextWroteStandsAtItsDefault) {
  EXPECT_TRUE(AllFourAreBack(ReadKeywordScope(StatesFour() + Restores())));
}

// The same text without the reset, which is what makes the case above about the
// reset rather than about four keywords no reading ever puts in effect. §34.4
// runs a keyword's scope on to the end of the compilation input, so all four
// are still standing where this reading stops.
TEST(ProtectResetDescription, WithoutItThoseKeywordsAreStillStanding) {
  ReadKeywordScope scope(StatesFour());
  EXPECT_EQ(scope.ValueOf(kDataKeyownerKeyword).value, kProvider);
  EXPECT_EQ(scope.ValueOf(kKeyMethodKeyword).value, kKeyCipher);
}

// §34.5.31.2 defines the expression as a synonym for the reset pragma directive
// §22.11.1 spells with protect in its keyword list, so the two spellings leave
// a text in the same place. A reading answering one of them and not the other
// would have one instruction mean two things.
TEST(ProtectResetDescription, ItRestoresWhatTheResetPragmaDirectiveRestores) {
  EXPECT_EQ(AllFourAreBack(ReadKeywordScope(StatesFour() + Restores())),
            AllFourAreBack(ReadKeywordScope(StatesFour() + ResetPragma())));
}

// §34.4 gives a keyword's value the position the reading has got to, so a
// keyword written after the reset is stated after it. Putting the values back
// does not take away the text's standing to state them again.
TEST(ProtectResetDescription, AKeywordWrittenAfterItIsInEffect) {
  ReadKeywordScope scope(StatesFour() + Restores() +
                         Writes(kDataKeyownerKeyword, kSecondProvider));
  EXPECT_EQ(scope.ValueOf(kDataKeyownerKeyword).value, kSecondProvider);
}

// DECRYPTION INPUT is none, so the expression is not one that delimits: a
// decryption envelope open where the reset is written is open after it, and the
// reset closed nothing.
TEST(ProtectResetDescription, ADecryptionEnvelopeIsNeitherOpenedNorClosed) {
  ReadWithTheKeys reading(std::string(kBeginProtected) + Restores());
  EXPECT_EQ(reading.StillOpen(), 1U);
  EXPECT_EQ(reading.Closed(), 0U);
}

// §34.4 has an envelope carry its own description and a reset follow the whole
// of it, so that the description does not stand over whatever the text goes on
// to hold. This tool writes such an envelope, and the reset it writes is one it
// answers: the data_method the envelope states about itself is back at its
// default where the envelope ends.
TEST(ProtectResetDescription, AnEnvelopeThisToolWroteDescribesNothingAfterIt) {
  ReadWithTheKeys reading(Encrypted(RegionWriting("")));
  EXPECT_TRUE(
      reading.reader.ProtectKeywords().ValueOf(kDataMethodKeyword).defaulted);
}

// ENCRYPTION INPUT holds of the tool that encrypts as well as of the one that
// reads. §34.5.10 and §34.5.12 have the entity and the name written for a
// region select the key it is encrypted under, and a reset between those names
// and the region takes them away: there is no key for the region to be
// encrypted under, so no block records it.
TEST(ProtectResetDescription, ARegionAfterItReachesNoNameWrittenBeforeIt) {
  std::string source = ReachesTheKey();
  source.append(Restores()).append(RegionAround(kSealedDesign));
  EXPECT_FALSE(Holds(Encrypted(source), kBlockOpening));
}

// The same text without the reset, which is what makes the case above about the
// reset rather than about names that reach no key wherever they are written.
TEST(ProtectResetDescription, WithoutItThoseNamesReachTheRegion) {
  std::string source = ReachesTheKey();
  source.append(RegionAround(kSealedDesign));
  EXPECT_TRUE(Holds(Encrypted(source), kBlockOpening));
}

// §34.5.31.2 puts the keywords back wherever the expression is written, and
// §34.4 makes no exception for the inside of an encryption envelope. A region
// that named its key and then reset has taken its own name away.
TEST(ProtectResetDescription, ARegionsOwnNamesGoBackWhenItResetsAfterThem) {
  std::string inside = ReachesTheKey();
  inside.append(Restores()).append(kSealedDesign);
  EXPECT_FALSE(Holds(Encrypted(RegionAround(inside)), kBlockOpening));
}

// The same two writings in the other order, which is what makes the case above
// about the reset standing after the names rather than about a region carrying
// one at all. Names written after the reset are stated after it and reach the
// key.
TEST(ProtectResetDescription, NamesWrittenAfterItInsideARegionReachTheKey) {
  std::string inside = Restores();
  inside.append(ReachesTheKey()).append(kSealedDesign);
  EXPECT_TRUE(Holds(Encrypted(RegionAround(inside)), kBlockOpening));
}

// ENCRYPTION OUTPUT is none: an envelope produced from a region that wrote a
// reset carries no reset expression on that account. The one standing in the
// cleartext of the envelope is the one §34.4 has follow it, so a region whose
// own reset had been published in the clear would have left two.
TEST(ProtectResetDescription, TheEnvelopeCarriesOnlyTheResetThatFollowsIt) {
  std::string inside = Restores();
  inside.append(ReachesTheKey()).append(kSealedDesign);
  EXPECT_EQ(TimesWritten(Encrypted(RegionAround(inside)), kResetExpression),
            1U);
}

// Where the region's own reset went instead. §34.5.1 has everything between the
// delimiters encrypted into the block unless a subclause holds it back, and
// §34.5.31.2 holds nothing back: the line is in the block with the rest of the
// region, which is what makes the case above about the cleartext rather than
// about a line that was dropped.
TEST(ProtectResetDescription, TheRegionsOwnResetIsInTheBlockWithTheRest) {
  std::string inside = Restores();
  inside.append(ReachesTheKey()).append(kSealedDesign);
  EXPECT_TRUE(
      Holds(OpenedBlockOf(Encrypted(RegionAround(inside))), kResetExpression));
}

// ---------------------------------------------------------------------------
// What a reset restores beyond the values a directive wrote against a keyword.
// ---------------------------------------------------------------------------

// §22.11.1 says a reset restores the default values *and state* of the
// pragma_keywords belonging to the pragma it names. The cases above ask about
// the values. Two kinds of state are held apart from those and are asked about
// here: a keyword still waiting for the line its definition speaks for, and a
// key §34.5.14 or §34.5.20 gave a keyword that came out of a key block as the
// key itself rather than as a name selecting one.

// The seven keywords that announce a value on the line beneath them wherever
// they stand inside a decryption envelope. §34.5.26, §34.5.13 and §34.5.19
// announce a public key, §34.5.27 and §34.5.15 announce a block, and §34.5.14
// and §34.5.20 announce the key that opens one.
//
// §34.5.22's is the eighth such keyword and is not among them.
// Preprocessor::ApplyAnnouncedBlockKeywords makes that announcement only where
// a block has already been recovered for a digest to vouch for, so an envelope
// carrying no block announces nothing there for a reset to drop.
constexpr std::string_view kAnnouncingKeywords[] = {
    "key_public_key",  "key_block",         "data_decrypt_key",
    "data_public_key", "digest_public_key", "digest_decrypt_key",
    "data_block",
};

// The line an announcement would otherwise take, written as design text so that
// what became of it can be read off what the preprocessor produced.
constexpr std::string_view kLineBeneath = "wire w;\n";

// A decryption envelope announcing `keyword`, with `also` standing on the same
// directive, and a line of design beneath.
//
// The reset is written on the announcing directive rather than on one of its
// own because a directive standing on the line beneath an announcement is the
// line that announcement speaks for. §34.5.13.2 and its six neighbours give the
// next line of the file to the value, and Preprocessor::TookAnnouncedValue
// excepts only the expression closing the envelope, so a reset written there
// would be taken for an encoded value and never reached. §22.11 writes a
// directive's expressions as a comma-separated list, so both stand on one line.
std::string AnnouncesThen(std::string_view keyword, std::string_view also) {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect ").append(keyword).append(also).append("\n");
  text.append(kLineBeneath);
  text.append("`pragma protect end_protected\n");
  return text;
}

// The key §34.5.14 has a text hand over, and the design a block sealed under it
// holds.
constexpr std::string_view kHandedOverKey = "the-session-key-of-this-envelope";
constexpr std::string_view kBlockedDesign = "module handed_over_m; endmodule\n";

// The two lines §34.5.14.1 spells that key over: the keyword standing alone,
// and the encoded value on the line beneath it, written under the coding scheme
// a text that stated none is read in.
std::string HandsOverTheKey() {
  std::string text = "`pragma protect data_decrypt_key\n";
  text.append(EncodeProtectBlock(kHandedOverKey, DefaultProtectEncoding()));
  text.append("\n");
  return text;
}

// An envelope handing that key over and then carrying a block sealed under it,
// with `between` standing after the key and before the block. No key is
// supplied to the reading, so the handed-over key is the only thing that opens
// the block.
std::string SealedUnderTheHandedOverKey(std::string_view between) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(HandsOverTheKey()).append(between);
  text.append("`pragma protect data_block\n");
  text.append(EncryptProtectedRegion(kBlockedDesign, kHandedOverKey));
  text.append("\n`pragma protect end_protected\n");
  return text;
}

// A keyword waiting for its line has been written and not yet answered, which
// is state within §22.11.1's meaning. After the reset nothing is waiting, so
// the line the announcement would have taken is design text and comes back out.
//
// Seven keywords are driven through it rather than one, a reset reaching the
// announcement it was written beside and leaving the other six standing being
// what a single keyword could not tell apart.
TEST(ProtectResetDescription, EveryAnnouncementAwaitingItsLineIsDropped) {
  for (std::string_view keyword : kAnnouncingKeywords) {
    PreprocFixture f;
    std::string read = Preprocess(AnnouncesThen(keyword, ", reset"), f);
    EXPECT_TRUE(Holds(read, kLineBeneath)) << keyword << " left: " << read;
  }
}

// The same seven envelopes without the reset, which is what makes the case
// above about the reset rather than about seven keywords that announce nothing.
// Each takes the line beneath it, and the design line does not come back out.
TEST(ProtectResetDescription, WithoutItEachAnnouncementTakesTheLineBeneathIt) {
  for (std::string_view keyword : kAnnouncingKeywords) {
    PreprocFixture f;
    std::string read = Preprocess(AnnouncesThen(keyword, ""), f);
    EXPECT_FALSE(Holds(read, kLineBeneath)) << keyword << " left: " << read;
  }
}

// §34.5.14 has the key a key block carried open the region's data block, and
// Preprocessor::ProtectKeyInEffect answers with it ahead of every name a text
// writes. It is the value of a protect pragma keyword, so §22.11.1 has the
// reset take it away: nothing then opens the block, and the design stays
// sealed.
//
// The reset stands on a directive of its own here, the line above it being the
// encoded key rather than a keyword still waiting for one.
TEST(ProtectResetDescription, TheSessionKeyTheTextHandedOverGoesBackToo) {
  PreprocFixture f;
  std::string read =
      Preprocess(SealedUnderTheHandedOverKey("`pragma protect reset\n"), f);
  EXPECT_FALSE(Holds(read, kBlockedDesign)) << read;
}

// The same envelope without the reset, which is what makes the case above about
// the reset rather than about a key that opened nothing wherever it stood. The
// key the text handed over opens the block and the design comes out of it.
TEST(ProtectResetDescription, WithoutItThatSessionKeyOpensTheBlock) {
  PreprocFixture f;
  std::string read = Preprocess(SealedUnderTheHandedOverKey(""), f);
  EXPECT_TRUE(Holds(read, kBlockedDesign)) << read;
}

// The key §34.5.20 has open a region's digest block, and the key its data block
// is under. The two differ at their first character rather than at some later
// one: CombineWithKey in src/preprocessor/protect_processing_cipher.cpp takes
// key[n % key.size()] for byte n, and a digest block is short enough that two
// keys agreeing over its opening characters would open it alike -- which would
// leave a case sealing the digest under the wrong key unable to fail.
constexpr std::string_view kDigestSessionKey = "unseals-the-digest-of-this-one";
constexpr std::string_view kDataBlockKey = "opens-the-data-of-this-one";

// The design the block holds, which is also what the digest beside it is
// computed over: §34.5.22 has a reader regenerate the digest from what the
// block above it recovered to, so the two have to be the same text.
constexpr std::string_view kVouchedDesign = "module vouched_m; endmodule\n";

// An envelope handing over the key that opens its digests, then carrying a data
// block under the key the reading holds, then a digest of what that block
// recovers to sealed under the handed-over key. `between` stands after the
// digest's key and before the block.
//
// The order is what §34.5.20.2 needs: Preprocessor::TakeDataBlockValue takes
// the digest's key at the line the data block stands on, so a key handed over
// after that block is handed over too late for the digest that follows it.
std::string VouchedForUnderTheDigestKey(std::string_view between) {
  ProtectEncoding encoding = DefaultProtectEncoding();
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect digest_decrypt_key\n");
  text.append(EncodeProtectBlock(kDigestSessionKey, encoding)).append("\n");
  text.append(between);
  text.append("`pragma protect data_block\n");
  text.append(EncryptProtectedRegion(kVouchedDesign, kDataBlockKey));
  text.append("\n");
  ProtectDigestBlockPolicy policy;
  policy.requested = true;
  policy.method = std::string(kDefaultDigestMethod);
  policy.key = std::string(kDigestSessionKey);
  text.append(ProtectDigestBlockDirectives(kVouchedDesign, policy, encoding));
  text.append("`pragma protect end_protected\n");
  return text;
}

// A reading of `src` by a tool holding the key the data block is under and no
// other, with the preprocessor kept alive afterwards.
//
// What §34.5.20 leaves behind is not output text but how a digest came out, and
// that belongs to the point the reading has got to rather than to any one
// directive, so it is read off the preprocessor once the whole text has passed
// through.
struct ReadHoldingTheBlockKey {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  explicit ReadHoldingTheBlockKey(const std::string& src)
      : pp(mgr, diag, TheBlockKeyOnly()) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  static PreprocConfig TheBlockKeyOnly() {
    PreprocConfig config;
    config.protect_key = std::string(kDataBlockKey);
    return config;
  }

  ProtectDigestCheck DigestCheck() const { return pp.LastDigestBlockCheck(); }
};

// §34.5.20 has the key a text hands over open the region's digests, and
// Preprocessor::DigestBlockKeyInEffect answers with it ahead of the names a
// text writes. It is the value of a protect pragma keyword, so §22.11.1 has the
// reset take it away: the digest is then opened under the key the data are
// under, which is not the key it was sealed with, so it does not open and the
// block it vouches for goes unchecked.
TEST(ProtectResetDescription, TheDigestSessionKeyGoesBackToo) {
  ReadHoldingTheBlockKey run(
      VouchedForUnderTheDigestKey("`pragma protect reset\n"));
  EXPECT_NE(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The same envelope without the reset, which is what makes the case above about
// the reset rather than about a digest no reading could have opened. The key
// the text handed over opens the digest, and it agrees with the block above it.
TEST(ProtectResetDescription, WithoutItThatDigestKeyOpensTheDigest) {
  ReadHoldingTheBlockKey run(VouchedForUnderTheDigestKey(""));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The object a viewport names and the access it asks for it. §34.5.32.2 leaves
// the access value an implementation-specific relaxation of protection, so no
// spelling of it is better than another and nothing here judges one.
constexpr std::string_view kViewportObject = "top.dut.mem";
constexpr std::string_view kOtherViewportObject = "top.dut.regfile";
constexpr std::string_view kViewportAccess = "read";

// A decryption envelope left open. §34.5.32.2 has a viewport describe objects
// of the envelope in force, and Preprocessor::ApplyViewport drops the list
// where an envelope opens or closes, so a case asking what a reset did to that
// list reads it back while the envelope that holds it still stands.
std::string OpensADecryptionEnvelope() {
  return "`pragma protect begin_protected\n";
}

// §34.5.31.2 restores all protect pragma keywords to their default values, and
// §34.4 tabulates viewport among them. Its default is no viewport, so an
// envelope that stated one and then reset describes nothing.
TEST(ProtectResetDescription, TheViewportsATextStatedGoBackToo) {
  ReadingViewports reading(OpensADecryptionEnvelope() +
                           ViewportOf(kViewportObject, kViewportAccess) +
                           Restores());
  EXPECT_EQ(reading.Count(), 0U) << reading.text;
}

// The same envelope without the reset, which is what makes the case above about
// the reset rather than about a viewport no reading ever gathered.
TEST(ProtectResetDescription, WithoutItThoseViewportsAreStillStanding) {
  ReadingViewports reading(OpensADecryptionEnvelope() +
                           ViewportOf(kViewportObject, kViewportAccess));
  EXPECT_EQ(reading.Count(), 1U) << reading.text;
}

// §34.4 gives a keyword's value the position the reading has got to, so a
// viewport written after the reset is stated after it. Without this case a
// reading that gathered no viewport at all would answer the two above.
TEST(ProtectResetDescription, AViewportWrittenAfterItIsRecorded) {
  ReadingViewports reading(OpensADecryptionEnvelope() +
                           ViewportOf(kViewportObject, kViewportAccess) +
                           Restores() +
                           ViewportOf(kOtherViewportObject, kViewportAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kOtherViewportObject);
}

// The defect stated directly: one keyword read both ways. What a directive
// wrote against the name is held in ProtectKeywordScope and the value parsed
// out of it in Preprocessor::protect_viewports_, and a reset that reached one
// and not the other would have the keyword report itself defaulted while the
// objects it named still stood.
TEST(ProtectResetDescription, TheTwoReadingsOfTheKeywordAgreeAfterIt) {
  ReadingViewports reading(OpensADecryptionEnvelope() +
                           ViewportOf(kViewportObject, kViewportAccess) +
                           Restores());
  EXPECT_TRUE(reading.pp.ProtectKeywords().ValueOf(kViewportKeyword).defaulted);
  EXPECT_EQ(reading.Count(), 0U) << reading.text;
}

}  // namespace
