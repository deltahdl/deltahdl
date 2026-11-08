#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_region.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

namespace {

constexpr std::string_view kAuthorName = "Ada Lovelace";
constexpr std::string_view kOtherAuthorName = "Grace Hopper";

constexpr std::string_view kDocumentation = "rev 3";

constexpr std::string_view kAnyNaming = "`pragma protect author";

constexpr std::string_view kKeyNameDirective =
    "`pragma protect data_keyname=\"acme-2026\"\n";

std::string NamesAuthor(std::string_view name) {
  std::string text = "`pragma protect author=\"";
  text.append(name).append("\"\n");
  return text;
}

std::string SealedModelNaming(std::string_view name) {
  return Encrypted(RegionWriting(NamesAuthor(name)));
}

struct ReadSource {
  static PreprocConfig KeyConfig() {
    PreprocConfig config;
    config.protect_keys = TheRegionsKey();
    return config;
  }

  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  explicit ReadSource(const std::string& src) : pp(mgr, diag, KeyConfig()) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  size_t OpenEnvelopes() const {
    return pp.ProtectEnvelopes().DecryptionEnvelopeDepth();
  }
  size_t ClosedEnvelopes() const {
    return pp.ProtectEnvelopes().ClosedEnvelopes().size();
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

std::string WithTheNamingMovedPastTheBlock(const std::string& written) {
  std::string naming = NamesAuthor(kAuthorName);
  size_t at = written.find(naming);
  if (at == std::string::npos) return written;
  std::string moved(written);
  moved.erase(at, naming.size());
  size_t closing = moved.find(kEndProtected);
  if (closing == std::string::npos) return written;
  moved.insert(closing, naming);
  return moved;
}

std::string WithTheKeyNameWrittenAsTheNaming(const std::string& written) {
  size_t at = written.find(kKeyNameDirective);
  if (at == std::string::npos) return written;
  std::string replaced(written);
  replaced.replace(at, kKeyNameDirective.size(), NamesAuthor(kKeyName));
  return replaced;
}

uint32_t TheNamedEnvelopesBlockLine(std::string_view envelope) {
  return LineHolding(envelope, kBlockOpening) + 1;
}

TEST(ProtectAuthorDescription, TheStringAgainstTheKeywordIsTheNameStated) {
  std::string written = Encrypted(RegionWriting(NamesAuthor(kAuthorName)));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, NamesAuthor(kAuthorName)));
}

TEST(ProtectAuthorDescription, AnIdentifierAgainstTheKeywordNamesTheAuthor) {
  std::string written =
      Encrypted(RegionWriting("`pragma protect author=ada_lovelace\n"));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, "`pragma protect author=ada_lovelace\n"));
}

TEST(ProtectAuthorDescription, ANumberAgainstTheKeywordNamesTheAuthor) {
  std::string written =
      Encrypted(RegionWriting("`pragma protect author=1843\n"));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, "`pragma protect author=1843\n"));
}

TEST(ProtectAuthorDescription, AnEmptyStringAgainstTheKeywordIsPlaced) {
  std::string written = Encrypted(RegionWriting(NamesAuthor("")));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, NamesAuthor("")));
}

TEST(ProtectAuthorDescription, AParenthesizedListSpecifiesNoName) {
  std::string listed =
      "`pragma protect author=(first=\"Ada\", last=\"Lovelace\")\n";
  std::string written = Encrypted(RegionWriting(listed));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyNaming));
  EXPECT_TRUE(Holds(OpenedBlockWriting(listed), listed));
}

TEST(ProtectAuthorDescription, ANameInsideADocumentationStringIsNotRecognized) {
  std::string documented =
      "`pragma protect comment=\"author=\\\"Ada Lovelace\\\"\"\n";
  std::string written = Encrypted(RegionWriting(documented));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_TRUE(Holds(written, documented));
  EXPECT_FALSE(Holds(written, kAnyNaming));
}

TEST(ProtectAuthorDescription, TheNameBesideADocumentationStringIsTheName) {
  std::string written = Encrypted(RegionWriting(
      "`pragma protect comment=\"rev 3\", author=\"Ada Lovelace\"\n"));
  EXPECT_TRUE(Holds(written, NamesAuthor(kAuthorName)));
  EXPECT_FALSE(Holds(written, NamesAuthor(kDocumentation)));
}

TEST(ProtectAuthorDescription, ThePlacedDirectiveStandsInsideTheEnvelope) {
  std::string written = Encrypted(RegionWriting(NamesAuthor(kAuthorName)));
  EXPECT_EQ(TimesWritten(written, NamesAuthor(kAuthorName)), 1U);
  EXPECT_LT(written.find(kBeginProtected),
            written.find(NamesAuthor(kAuthorName)));
  EXPECT_LT(written.find(NamesAuthor(kAuthorName)),
            written.find(kEndProtected));
}

TEST(ProtectAuthorDescription, ARegionNamingNobodyPlacesNoDirective) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(kSealedDesign);
  std::string written = Encrypted(RegionAround(enclosed));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyNaming));
}

TEST(ProtectAuthorDescription, AnEnclosedSealedModelsNameIsNotPlacedAgain) {
  std::string enclosed = SealedModelNaming(kOtherAuthorName);
  enclosed.append(ReachesTheKey());
  enclosed.append(NamesAuthor(kAuthorName));
  enclosed.append(kSealedDesign);
  std::string written = Encrypted(RegionAround(enclosed));
  EXPECT_EQ(TimesWritten(written, NamesAuthor(kAuthorName)), 1U);
  EXPECT_FALSE(Holds(written, kOtherAuthorName));
}

TEST(ProtectAuthorDescription, AnEnclosedSealedModelsNameTravelsIntoTheBlock) {
  std::string enclosed = SealedModelNaming(kOtherAuthorName);
  enclosed.append(ReachesTheKey());
  enclosed.append(NamesAuthor(kAuthorName));
  enclosed.append(kSealedDesign);
  std::string opened = OpenedBlockOf(Encrypted(RegionAround(enclosed)));
  EXPECT_TRUE(Holds(opened, kBeginProtected));
  EXPECT_TRUE(Holds(opened, NamesAuthor(kOtherAuthorName)));
}

TEST(ProtectAuthorDescription, AnEnvelopePlacesOnlyItsOwnRegionsName) {
  std::string second = ReachesTheKey();
  second.append("module other_m; endmodule\n");
  std::string written =
      Encrypted(RegionWriting(NamesAuthor(kAuthorName)) + RegionAround(second));
  EXPECT_EQ(TimesWritten(written, kBeginProtected), 2U);
  EXPECT_EQ(TimesWritten(written, kAnyNaming), 1U);
  size_t first_envelope = written.find(kBeginProtected);
  size_t second_envelope = written.find(kBeginProtected, first_envelope + 1);
  EXPECT_LT(written.find(kAnyNaming), second_envelope);
}

TEST(ProtectAuthorDescription, TheOpenedBlockHoldsNoNamingDirective) {
  std::string opened = OpenedBlockWriting(NamesAuthor(kAuthorName));
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyNaming));
}

TEST(ProtectAuthorDescription, AnAuthorNamedByAnIdentifierIsKeptOut) {
  std::string opened =
      OpenedBlockWriting("`pragma protect author=ada_lovelace\n");
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyNaming));
}

TEST(ProtectAuthorDescription, AnEmptyStringNamingIsKeptOutOfTheBlock) {
  std::string opened = OpenedBlockWriting(NamesAuthor(""));
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyNaming));
}

TEST(ProtectAuthorDescription, TheBlockIsTheOneTheUnnamedRegionProduces) {
  std::string named = Encrypted(RegionWriting(NamesAuthor(kAuthorName)));
  std::string unnamed = Encrypted(RegionWriting(""));
  EXPECT_FALSE(DataBlockOf(unnamed).empty());
  EXPECT_EQ(DataBlockOf(named), DataBlockOf(unnamed));
}

TEST(ProtectAuthorDescription, TheKeywordStandingAloneIsLeftInTheBlock) {
  std::string bare = "`pragma protect author\n";
  EXPECT_FALSE(Holds(Encrypted(RegionWriting(bare)), kAnyNaming));
  EXPECT_TRUE(Holds(OpenedBlockWriting(bare), bare));
}

TEST(ProtectAuthorDescription, AnExpressionOutsideEveryEnvelopeIsCopied) {
  std::string src = "module m;\n";
  src.append("`pragma  protect   author  =  \"Ada Lovelace\" // who\n");
  src.append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

TEST(ProtectAuthorDescription, AnExpressionBetweenTwoRegionsIsCopiedInPlace) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(kSealedDesign);
  std::string src = RegionAround(enclosed);
  src.append(NamesAuthor(kAuthorName));
  src.append(RegionAround(enclosed));
  std::string written = Encrypted(src);
  EXPECT_EQ(TimesWritten(written, kAnyNaming), 1U);
  EXPECT_LT(written.find(kEndProtected), written.find(kAnyNaming));
  size_t first_envelope = written.find(kBeginProtected);
  size_t second_envelope = written.find(kBeginProtected, first_envelope + 1);
  EXPECT_LT(written.find(kAnyNaming), second_envelope);
}

TEST(ProtectAuthorDescription, AnExpressionInAPassingSealedModelIsCopied) {
  std::string src = "module m;\n";
  src.append(SealedModelNaming(kAuthorName));
  src.append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

TEST(ProtectAuthorDescription, ARegionReachingNoKeyKeepsItsNamingAsWritten) {
  std::string src = RegionWriting(NamesAuthor(kAuthorName));
  EXPECT_EQ(EncryptedWithoutTheKey(src), src);
}

TEST(ProtectAuthorDescription, TheNameReachesNoneOfTheRecoveredDesign) {
  ReadSource read(Encrypted(RegionWriting(NamesAuthor(kAuthorName))));
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kAuthorName));
}

TEST(ProtectAuthorDescription, TwoEnvelopesDifferingOnlyInTheNameReadAlike) {
  std::string named = Encrypted(RegionWriting(NamesAuthor(kAuthorName)));
  std::string other = Encrypted(RegionWriting(NamesAuthor(kOtherAuthorName)));
  ASSERT_NE(named, other);
  ReadSource read(named);
  ReadSource read_other(other);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read_other.diag.HasErrors());
  EXPECT_EQ(read.text, read_other.text);
}

TEST(ProtectAuthorDescription, ANamingPastTheBlockCostsTheReadingNothing) {
  std::string moved = WithTheNamingMovedPastTheBlock(
      Encrypted(RegionWriting(NamesAuthor(kAuthorName))));
  ASSERT_LT(moved.find(kBlockOpening), moved.find(NamesAuthor(kAuthorName)));
  ReadSource read(moved);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kAuthorName));
}

TEST(ProtectAuthorDescription, AnEnvelopeStatingOnlyANameIsReadAndClosed) {
  std::string envelope(kBeginProtected);
  envelope.append(NamesAuthor(kAuthorName)).append(kEndProtected);
  ReadSource read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_EQ(read.ClosedEnvelopes(), 1U);
  EXPECT_EQ(read.OpenEnvelopes(), 0U);
  EXPECT_FALSE(read.Holds(kAuthorName));
  EXPECT_TRUE(read.Holds("endmodule"));
}

TEST(ProtectAuthorDescription, ANameSpellingAKeyNameOpensNothing) {
  std::string replaced = WithTheKeyNameWrittenAsTheNaming(
      Encrypted(RegionWriting(NamesAuthor(kAuthorName))));
  ASSERT_TRUE(Holds(replaced, NamesAuthor(kKeyName)));
  ReadSource read(replaced);
  EXPECT_TRUE(ReportedError(
      read.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      TheNamedEnvelopesBlockLine(replaced), "34.3.2"));
  EXPECT_FALSE(read.Holds("module sealed_m"));
}

}  // namespace
