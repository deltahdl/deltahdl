#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_region.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kAuthorName = "Ada Lovelace";
constexpr std::string_view kAuthorDirective =
    "`pragma protect author=\"Ada Lovelace\"\n";

constexpr std::string_view kOtherAuthorName = "Grace Hopper";

std::string NamesAuthor(std::string_view name) {
  std::string text = "`pragma protect author=\"";
  text.append(name).append("\"\n");
  return text;
}

std::string NamesAuthorBesideKeyName(std::string_view name) {
  std::string text = "`pragma protect author=\"";
  text.append(name).append("\", data_keyname=\"");
  text.append(kKeyName).append("\"\n");
  return text;
}

std::string PreviouslyProtected(const std::string& enclosed) {
  std::string text(kBeginProtected);
  text.append(enclosed);
  text.append(kEndProtected);
  return text;
}

std::string EncryptedUnder(const std::string& src, const ProtectKeyList& keys) {
  return EncryptEnvelopes(src, "", keys);
}

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

TEST(ProtectAuthorEncryptionInput, TheStringAgainstTheKeywordNamesTheAuthor) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find(kAuthorDirective), std::string::npos);
}

TEST(ProtectAuthorEncryptionInput, TheKeywordStandingAloneNamesNobody) {
  std::string enclosed = ReachesTheKey();
  enclosed.append("`pragma protect author\n").append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find(kBeginProtected), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect author"), std::string::npos);
}

TEST(ProtectAuthorEncryptionInput, ADocumentationStringNamesNoAuthor) {
  std::string enclosed = ReachesTheKey();
  enclosed.append("`pragma protect comment=\"Ada Lovelace\"\n");
  enclosed.append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find(kBeginProtected), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect author"), std::string::npos);
}

TEST(ProtectAuthorEncryptionInput, TheAuthorIsTakenApartFromTheDocumentation) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName));
  enclosed.append("`pragma protect comment=\"Grace Hopper\"\n");
  enclosed.append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find(kAuthorDirective), std::string::npos);
  EXPECT_EQ(encrypted.find(NamesAuthor(kOtherAuthorName)), std::string::npos);
}

TEST(ProtectAuthorEncryptionOutput, TheDirectiveStandsInsideTheEnvelope) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_EQ(TimesWritten(encrypted, kAuthorDirective), 1U);
  EXPECT_LT(encrypted.find(kBeginProtected), encrypted.find(kAuthorDirective));
  EXPECT_LT(encrypted.find(kAuthorDirective), encrypted.find(kEndProtected));
}

TEST(ProtectAuthorEncryptionOutput, TheDirectiveStandsAheadOfTheBlock) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find(kBlockOpening), std::string::npos);
  EXPECT_LT(encrypted.find(kAuthorDirective), encrypted.find(kBlockOpening));
}

TEST(ProtectAuthorEncryptionOutput, ARegionNamingNoAuthorWritesNoDirective) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find(kBeginProtected), std::string::npos);
  EXPECT_EQ(encrypted.find("`pragma protect author"), std::string::npos);
}

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

TEST(ProtectAuthorEncryptionOutput, ANumberValueIsPlacedAsItWasWritten) {
  std::string enclosed = ReachesTheKey();
  enclosed.append("`pragma protect author=1843\n").append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find("`pragma protect author=1843\n"), std::string::npos);
}

TEST(ProtectAuthorEncryptionOutput, AnExpressionSharingADirectiveIsPlaced) {
  std::string enclosed = DesignatesTheProvider();
  enclosed.append(NamesAuthorBesideKeyName(kAuthorName));
  enclosed.append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find(kAuthorDirective), std::string::npos);
}

TEST(ProtectAuthorEncryptionOutput, TheLatestNamingInTheRegionIsTheOnePlaced) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName));
  enclosed.append(NamesAuthor(kOtherAuthorName)).append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_EQ(TimesWritten(encrypted, NamesAuthor(kOtherAuthorName)), 1U);
  EXPECT_EQ(encrypted.find(kAuthorDirective), std::string::npos);
}

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

TEST(ProtectAuthorEncryptionOutput, TheOpenedBlockHoldsNoNaming) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  std::string opened = OpenedBlockOf(Encrypted(RegionAround(enclosed)));
  EXPECT_NE(opened.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(opened.find("`pragma protect author"), std::string::npos);
}

TEST(ProtectAuthorEncryptionOutput, ASharedDirectivesNamingIsKeptOut) {
  std::string enclosed = DesignatesTheProvider();
  enclosed.append(NamesAuthorBesideKeyName(kAuthorName));
  enclosed.append(kSealedDesign);
  std::string opened = OpenedBlockOf(Encrypted(RegionAround(enclosed)));
  EXPECT_NE(opened.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(opened.find(kAuthorName), std::string::npos);
}

TEST(ProtectAuthorEncryptionOutput, TheKeywordStandingAloneIsEncrypted) {
  std::string enclosed = ReachesTheKey();
  enclosed.append("`pragma protect author\n").append(kSealedDesign);
  std::string opened = OpenedBlockOf(Encrypted(RegionAround(enclosed)));
  EXPECT_NE(opened.find("`pragma protect author\n"), std::string::npos);
}

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

TEST(ProtectAuthorEncryptionOutput, TheStatedBlockSizeExcludesTheNaming) {
  std::string named = ReachesTheKey();
  named.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  std::string unnamed = ReachesTheKey();
  unnamed.append(kSealedDesign);
  std::string bytes = "bytes=";
  bytes.append(std::to_string(ProtectedRegionBlockSize(unnamed))).append(")");
  EXPECT_NE(Encrypted(RegionAround(named)).find(bytes), std::string::npos);
}

TEST(ProtectAuthorEncryptionOutput, ANamingInsideASealedModelIsNotPlaced) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(PreviouslyProtected(NamesAuthor(kAuthorName)));
  enclosed.append(kSealedDesign);
  std::string encrypted = Encrypted(RegionAround(enclosed));
  EXPECT_NE(encrypted.find(kBeginProtected), std::string::npos);
  EXPECT_EQ(encrypted.find(kAuthorDirective), std::string::npos);
}

TEST(ProtectAuthorEncryptionOutput, ANamingInsideASealedModelIsEncrypted) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(PreviouslyProtected(NamesAuthor(kAuthorName)));
  enclosed.append(kSealedDesign);
  std::string opened = OpenedBlockOf(Encrypted(RegionAround(enclosed)));
  EXPECT_NE(opened.find(kAuthorDirective), std::string::npos);
}

TEST(ProtectAuthorEncryptionOutput, AnExpressionOutsideEveryEnvelopeIsCopied) {
  std::string src = "module m;\n";
  src.append("`pragma  protect   author  =  \"Ada Lovelace\"\n");
  src.append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

TEST(ProtectAuthorEncryptionOutput, AnExpressionAheadOfTheEnvelopeIsCopied) {
  std::string src = NamesAuthor(kAuthorName);
  std::string enclosed = ReachesTheKey();
  enclosed.append(kSealedDesign);
  src.append(RegionAround(enclosed));
  std::string encrypted = Encrypted(src);
  EXPECT_EQ(TimesWritten(encrypted, kAuthorDirective), 1U);
  EXPECT_LT(encrypted.find(kAuthorDirective), encrypted.find(kBeginProtected));
}

TEST(ProtectAuthorEncryptionOutput, AnExpressionAfterTheEnvelopeIsCopied) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(kSealedDesign);
  std::string src = RegionAround(enclosed) + NamesAuthor(kAuthorName);
  std::string encrypted = Encrypted(src);
  EXPECT_EQ(TimesWritten(encrypted, kAuthorDirective), 1U);
  EXPECT_LT(encrypted.find(kEndProtected), encrypted.find(kAuthorDirective));
}

TEST(ProtectAuthorEncryptionOutput, ARegionWithNoKeyKeepsItsNamingAsWritten) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  std::string src = RegionAround(enclosed);
  EXPECT_EQ(EncryptedUnder(src, AKeyUnderAnotherName()), src);
}

TEST(ProtectAuthorDecryptionInput, TheNameReachesNoneOfTheDesignText) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  ReadUnderRegionKeys read(Encrypted(RegionAround(enclosed)));
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kAuthorName));
}

TEST(ProtectAuthorDecryptionInput, TheNameCostsTheReadingNothing) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(NamesAuthor(kAuthorName)).append(kSealedDesign);
  ReadUnderRegionKeys read(Encrypted(RegionAround(enclosed)));
  EXPECT_FALSE(read.diag.HasErrors());
}

TEST(ProtectAuthorDecryptionInput, AForeignEnvelopeNamingAnAuthorIsRead) {
  std::string envelope(kBeginProtected);
  envelope.append(NamesAuthor(kAuthorName)).append(kEndProtected);
  ReadUnderRegionKeys read(envelope);
  EXPECT_FALSE(read.Holds(kAuthorName));
}

}  // namespace
