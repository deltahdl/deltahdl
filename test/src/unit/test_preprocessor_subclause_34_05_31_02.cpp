#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "helpers_protect_keyword_value.h"
#include "helpers_protect_region.h"
#include "helpers_text_lines.h"
#include "preprocessor/protect_keywords.h"

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
const std::string kRestores = "`pragma protect reset\n";

// The directive §22.11.1 defines with protect in its pragma keyword list, which
// §34.5.31.2 says the expression above is a synonym for.
const std::string kResetPragma = "`pragma reset protect\n";

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
  EXPECT_TRUE(AllFourAreBack(ReadKeywordScope(StatesFour() + kRestores)));
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
  EXPECT_EQ(AllFourAreBack(ReadKeywordScope(StatesFour() + kRestores)),
            AllFourAreBack(ReadKeywordScope(StatesFour() + kResetPragma)));
}

// §34.4 gives a keyword's value the position the reading has got to, so a
// keyword written after the reset is stated after it. Putting the values back
// does not take away the text's standing to state them again.
TEST(ProtectResetDescription, AKeywordWrittenAfterItIsInEffect) {
  ReadKeywordScope scope(StatesFour() + kRestores +
                         Writes(kDataKeyownerKeyword, kSecondProvider));
  EXPECT_EQ(scope.ValueOf(kDataKeyownerKeyword).value, kSecondProvider);
}

// DECRYPTION INPUT is none, so the expression is not one that delimits: a
// decryption envelope open where the reset is written is open after it, and the
// reset closed nothing.
TEST(ProtectResetDescription, ADecryptionEnvelopeIsNeitherOpenedNorClosed) {
  ReadWithTheKeys reading(std::string(kBeginProtected) + kRestores);
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
  source.append(kRestores).append(RegionAround(kSealedDesign));
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
  inside.append(kRestores).append(kSealedDesign);
  EXPECT_FALSE(Holds(Encrypted(RegionAround(inside)), kBlockOpening));
}

// The same two writings in the other order, which is what makes the case above
// about the reset standing after the names rather than about a region carrying
// one at all. Names written after the reset are stated after it and reach the
// key.
TEST(ProtectResetDescription, NamesWrittenAfterItInsideARegionReachTheKey) {
  std::string inside = kRestores;
  inside.append(ReachesTheKey()).append(kSealedDesign);
  EXPECT_TRUE(Holds(Encrypted(RegionAround(inside)), kBlockOpening));
}

// ENCRYPTION OUTPUT is none: an envelope produced from a region that wrote a
// reset carries no reset expression on that account. The one standing in the
// cleartext of the envelope is the one §34.4 has follow it, so a region whose
// own reset had been published in the clear would have left two.
TEST(ProtectResetDescription, TheEnvelopeCarriesOnlyTheResetThatFollowsIt) {
  std::string inside = kRestores;
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
  std::string inside = kRestores;
  inside.append(ReachesTheKey()).append(kSealedDesign);
  EXPECT_TRUE(
      Holds(OpenedBlockOf(Encrypted(RegionAround(inside))), kResetExpression));
}

}  // namespace
