#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "helpers_protect_region.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"

using namespace delta;

namespace {

constexpr std::string_view kFurtherWord = "Analytical Society, London";
constexpr std::string_view kOtherFurtherWord = "Harvard Computation Lab";

constexpr std::string_view kDocumentation = "rev 3";

constexpr std::string_view kAuthorName = "Ada Lovelace";

constexpr std::string_view kAnyStating = "`pragma protect author_info=";

constexpr std::string_view kAnyNaming = "`pragma protect author=";

std::string StatesFurther(std::string_view word) {
  std::string written = "`pragma protect author_info=\"";
  written.append(word).append("\"\n");
  return written;
}

std::string NamesTheAuthor(std::string_view name) {
  std::string written = "`pragma protect author=\"";
  written.append(name).append("\"\n");
  return written;
}

std::string SealedModelStating(std::string_view word) {
  return Encrypted(RegionWriting(StatesFurther(word)));
}

std::string WithTheStatementMovedPastTheBlock(const std::string& envelope) {
  std::string stating = StatesFurther(kFurtherWord);
  size_t stands = envelope.find(stating);
  if (stands == std::string::npos) return envelope;
  std::string moved(envelope);
  moved.erase(stands, stating.size());
  size_t closes = moved.find(kEndProtected);
  if (closes == std::string::npos) return envelope;
  moved.insert(closes, stating);
  return moved;
}

std::string WithTheKeyNameWrittenAsTheStatement(const std::string& envelope) {
  std::string designation = DesignatesTheKey();
  size_t stands = envelope.find(designation);
  if (stands == std::string::npos) return envelope;
  std::string replaced(envelope);
  replaced.replace(stands, designation.size(), StatesFurther(kKeyName));
  return replaced;
}

uint32_t WhereTheOfferingsBlockStands(std::string_view envelope) {
  return LineHolding(envelope, kBlockOpening) + 1;
}

TEST(ProtectAuthorInfoDescription, TheStringAgainstTheKeywordIsWhatIsOffered) {
  std::string written = Encrypted(RegionWriting(StatesFurther(kFurtherWord)));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, StatesFurther(kFurtherWord)));
}

TEST(ProtectAuthorInfoDescription, AnIdentifierAgainstTheKeywordIsOffered) {
  std::string named = "`pragma protect author_info=analytical_society\n";
  std::string written = Encrypted(RegionWriting(named));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, named));
}

TEST(ProtectAuthorInfoDescription, AnEmptyStringAgainstTheKeywordIsPlaced) {
  std::string written = Encrypted(RegionWriting(StatesFurther("")));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, StatesFurther("")));
}

TEST(ProtectAuthorInfoDescription, AParenthesizedListSpecifiesNothing) {
  std::string listed =
      "`pragma protect author_info=(city=\"London\", year=1843)\n";
  std::string written = Encrypted(RegionWriting(listed));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyStating));
  EXPECT_TRUE(Holds(OpenedBlockWriting(listed), listed));
}

TEST(ProtectAuthorInfoDescription, WordsInsideADocumentationStringAreNotTaken) {
  std::string documented =
      "`pragma protect comment=\"author_info=\\\"Analytical Society\\\"\"\n";
  std::string written = Encrypted(RegionWriting(documented));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_TRUE(Holds(written, documented));
  EXPECT_FALSE(Holds(written, kAnyStating));
}

TEST(ProtectAuthorInfoDescription, TheValueBesideADocumentationStringIsTaken) {
  std::string beside = "`pragma protect comment=\"rev 3\", ";
  beside.append("author_info=\"Analytical Society, London\"\n");
  std::string written = Encrypted(RegionWriting(beside));
  EXPECT_TRUE(Holds(written, StatesFurther(kFurtherWord)));
  EXPECT_FALSE(Holds(written, StatesFurther(kDocumentation)));
}

TEST(ProtectAuthorInfoDescription, TheOfferingIsNotTakenForTheAuthorsName) {
  std::string written = Encrypted(RegionWriting(StatesFurther(kFurtherWord)));
  EXPECT_TRUE(Holds(written, StatesFurther(kFurtherWord)));
  EXPECT_FALSE(Holds(written, kAnyNaming));
}

TEST(ProtectAuthorInfoDescription, TheAuthorsNameIsNotTakenAsTheOffering) {
  std::string written = Encrypted(RegionWriting(NamesTheAuthor(kAuthorName)));
  EXPECT_TRUE(Holds(written, kAnyNaming));
  EXPECT_FALSE(Holds(written, kAnyStating));
}

TEST(ProtectAuthorInfoDescription, ThePlacedDirectiveStandsInsideTheEnvelope) {
  std::string written = Encrypted(RegionWriting(StatesFurther(kFurtherWord)));
  EXPECT_EQ(TimesWritten(written, StatesFurther(kFurtherWord)), 1U);
  EXPECT_LT(written.find(kBeginProtected),
            written.find(StatesFurther(kFurtherWord)));
  EXPECT_LT(written.find(StatesFurther(kFurtherWord)),
            written.find(kEndProtected));
}

TEST(ProtectAuthorInfoDescription, ARegionOfferingNothingPlacesNoDirective) {
  std::string inside = ReachesTheKey();
  inside.append(kSealedDesign);
  std::string written = Encrypted(RegionAround(inside));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyStating));
}

TEST(ProtectAuthorInfoDescription, AnEnclosedSealedModelsWordIsNotPlacedAgain) {
  std::string inside = SealedModelStating(kOtherFurtherWord);
  inside.append(ReachesTheKey());
  inside.append(StatesFurther(kFurtherWord));
  inside.append(kSealedDesign);
  std::string written = Encrypted(RegionAround(inside));
  EXPECT_EQ(TimesWritten(written, StatesFurther(kFurtherWord)), 1U);
  EXPECT_FALSE(Holds(written, kOtherFurtherWord));
}

TEST(ProtectAuthorInfoDescription, AnEnclosedSealedModelsOfferingIsCarriedIn) {
  std::string inside = SealedModelStating(kOtherFurtherWord);
  inside.append(ReachesTheKey());
  inside.append(StatesFurther(kFurtherWord));
  inside.append(kSealedDesign);
  std::string opened = OpenedBlockOf(Encrypted(RegionAround(inside)));
  EXPECT_TRUE(Holds(opened, kBeginProtected));
  EXPECT_TRUE(Holds(opened, StatesFurther(kOtherFurtherWord)));
}

TEST(ProtectAuthorInfoDescription, AnEnvelopePlacesOnlyItsOwnRegionsOffering) {
  std::string second = ReachesTheKey();
  second.append("module other_m; endmodule\n");
  std::string first = RegionWriting(StatesFurther(kFurtherWord));
  std::string written = Encrypted(first + RegionAround(second));
  EXPECT_EQ(TimesWritten(written, kBeginProtected), 2U);
  EXPECT_EQ(TimesWritten(written, kAnyStating), 1U);
  size_t opens_first = written.find(kBeginProtected);
  size_t opens_second = written.find(kBeginProtected, opens_first + 1);
  EXPECT_LT(written.find(kAnyStating), opens_second);
}

TEST(ProtectAuthorInfoDescription, TheOpenedBlockHoldsNoStatingDirective) {
  std::string opened = OpenedBlockWriting(StatesFurther(kFurtherWord));
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyStating));
}

TEST(ProtectAuthorInfoDescription, AnOfferingWrittenAsAnIdentifierIsKeptOut) {
  std::string named = "`pragma protect author_info=analytical_society\n";
  std::string opened = OpenedBlockWriting(named);
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyStating));
}

TEST(ProtectAuthorInfoDescription, AnEmptyStringOfferingIsKeptOutOfTheBlock) {
  std::string opened = OpenedBlockWriting(StatesFurther(""));
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyStating));
}

TEST(ProtectAuthorInfoDescription, TheBlockIsTheOneTheSilentRegionProduces) {
  std::string offered = Encrypted(RegionWriting(StatesFurther(kFurtherWord)));
  std::string silent = Encrypted(RegionWriting(""));
  EXPECT_FALSE(DataBlockOf(silent).empty());
  EXPECT_EQ(DataBlockOf(offered), DataBlockOf(silent));
}

TEST(ProtectAuthorInfoDescription, TheKeywordStandingAloneIsLeftInTheBlock) {
  std::string bare = "`pragma protect author_info\n";
  EXPECT_FALSE(Holds(Encrypted(RegionWriting(bare)), kAnyStating));
  EXPECT_TRUE(Holds(OpenedBlockWriting(bare), bare));
}

TEST(ProtectAuthorInfoDescription, AnExpressionOutsideEveryEnvelopeIsCopied) {
  std::string spaced = "`pragma  protect   author_info  =  ";
  spaced.append("\"Analytical Society, London\" // more\n");
  std::string src = "module m;\n";
  src.append(spaced).append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

TEST(ProtectAuthorInfoDescription, AnExpressionBetweenTwoRegionsStaysInPlace) {
  std::string inside = ReachesTheKey();
  inside.append(kSealedDesign);
  std::string src = RegionAround(inside);
  src.append(StatesFurther(kFurtherWord));
  src.append(RegionAround(inside));
  std::string written = Encrypted(src);
  EXPECT_EQ(TimesWritten(written, kAnyStating), 1U);
  EXPECT_LT(written.find(kEndProtected), written.find(kAnyStating));
  size_t opens_first = written.find(kBeginProtected);
  size_t opens_second = written.find(kBeginProtected, opens_first + 1);
  EXPECT_LT(written.find(kAnyStating), opens_second);
}

TEST(ProtectAuthorInfoDescription, AnExpressionInAPassingSealedModelIsCopied) {
  std::string src = "module m;\n";
  src.append(SealedModelStating(kFurtherWord));
  src.append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

TEST(ProtectAuthorInfoDescription, ARegionReachingNoKeyKeepsItsOfferingAsIs) {
  std::string src = RegionWriting(StatesFurther(kFurtherWord));
  EXPECT_EQ(EncryptedWithoutTheKey(src), src);
}

TEST(ProtectAuthorInfoDescription, TheOfferingReachesNoneOfTheRecoveredDesign) {
  ReadWithTheKeys read(Encrypted(RegionWriting(StatesFurther(kFurtherWord))));
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kFurtherWord));
}

TEST(ProtectAuthorInfoDescription, TwoEnvelopesDifferingOnlyInTheOfferingRead) {
  std::string offered = Encrypted(RegionWriting(StatesFurther(kFurtherWord)));
  std::string other =
      Encrypted(RegionWriting(StatesFurther(kOtherFurtherWord)));
  ASSERT_NE(offered, other);
  ReadWithTheKeys read(offered);
  ReadWithTheKeys read_other(other);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_FALSE(read_other.diags.HasErrors());
  EXPECT_EQ(read.produced, read_other.produced);
}

TEST(ProtectAuthorInfoDescription, AnOfferingPastTheBlockCostsTheReadingNone) {
  std::string moved = WithTheStatementMovedPastTheBlock(
      Encrypted(RegionWriting(StatesFurther(kFurtherWord))));
  ASSERT_LT(moved.find(kBlockOpening), moved.find(StatesFurther(kFurtherWord)));
  ReadWithTheKeys read(moved);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kFurtherWord));
}

TEST(ProtectAuthorInfoDescription, AnEnvelopeStatingOnlyAnOfferingIsClosed) {
  std::string envelope(kBeginProtected);
  envelope.append(StatesFurther(kFurtherWord)).append(kEndProtected);
  ReadWithTheKeys read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_EQ(read.Closed(), 1U);
  EXPECT_EQ(read.StillOpen(), 0U);
  EXPECT_FALSE(read.Produced(kFurtherWord));
  EXPECT_TRUE(read.Produced("endmodule"));
}

TEST(ProtectAuthorInfoDescription, AnOfferingSpellingAKeyNameOpensNothing) {
  std::string replaced = WithTheKeyNameWrittenAsTheStatement(
      Encrypted(RegionWriting(StatesFurther(kFurtherWord))));
  ASSERT_TRUE(Holds(replaced, StatesFurther(kKeyName)));
  ReadWithTheKeys read(replaced);
  EXPECT_TRUE(ReportedError(
      read.diags.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      WhereTheOfferingsBlockStands(replaced), "34.3.2"));
  EXPECT_FALSE(read.Produced("module sealed_m"));
}

}  // namespace
