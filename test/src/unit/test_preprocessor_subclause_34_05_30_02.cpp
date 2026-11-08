#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "helpers_protect_region.h"
#include "helpers_text_lines.h"

using namespace delta;

namespace {

constexpr std::string_view kNotice = "Copyright 2026 Acme Corp";
constexpr std::string_view kOtherNotice = "Patent pending, Acme Corp";

constexpr std::string_view kAnyDocumenting = "`pragma protect comment";

constexpr std::string_view kBlockCounting = "`pragma protect encoding=";

constexpr std::string_view kAnyDirective = "`pragma protect ";

constexpr std::string_view kUnheldDataKeyName = "design-2027";

std::string Documents(std::string_view notice) {
  std::string text = "`pragma protect comment=\"";
  text.append(notice).append("\"\n");
  return text;
}

std::string SealedModelDocumenting(std::string_view notice) {
  return Encrypted(RegionWriting(Documents(notice)));
}

std::string BetweenTheCommentAndTheBlock(const std::string& written,
                                         std::string_view notice) {
  std::string documenting = Documents(notice);
  size_t at = written.find(documenting);
  if (at == std::string::npos) return written;
  size_t from = at + documenting.size();
  size_t to = written.find(kBlockOpening, from);
  if (to == std::string::npos) return written;
  return written.substr(from, to - from);
}

std::string RegionBehindAKeyBlock(std::string_view written) {
  std::string inside = "`pragma protect data_keyowner=\"";
  inside.append(kKeyOwner).append("\"\n");
  inside.append("`pragma protect data_keyname=\"");
  inside.append(kUnheldDataKeyName).append("\"\n");
  inside.append("`pragma protect key_keyowner=\"");
  inside.append(kKeyOwner).append("\"\n");
  inside.append("`pragma protect key_keyname=\"");
  inside.append(kKeyName).append("\"\n");
  inside.append(written).append(kSealedDesign);
  return RegionAround(inside);
}

TEST(ProtectCommentDescription, TheEntireCommentIncludingThePragmaIsOutput) {
  std::string written = Encrypted(RegionWriting(Documents(kNotice)));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_EQ(TimesWritten(written, Documents(kNotice)), 1U);
}

TEST(ProtectCommentDescription, TheOutputCommentStandsInsideTheEnvelope) {
  std::string written = Encrypted(RegionWriting(Documents(kNotice)));
  EXPECT_LT(written.find(kBeginProtected), written.find(kAnyDocumenting));
  EXPECT_LT(written.find(kAnyDocumenting), written.find(kEndProtected));
}

TEST(ProtectCommentDescription, ARegionDocumentingNothingOutputsNoComment) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyDocumenting));
}

TEST(ProtectCommentDescription, AnEmptyStringAgainstTheKeywordIsOutput) {
  std::string written = Encrypted(RegionWriting(Documents("")));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, Documents("")));
}

TEST(ProtectCommentDescription, ANoticeWrittenBareIsOutputBare) {
  std::string bare = "`pragma protect comment=copyright_acme_2026\n";
  std::string written = Encrypted(RegionWriting(bare));
  EXPECT_TRUE(Holds(written, bare));
  EXPECT_FALSE(Holds(written, "comment=\"copyright_acme_2026\""));
}

TEST(ProtectCommentDescription, AParenthesizedListDocumentsNothing) {
  std::string listed = "`pragma protect comment=(notice=\"acme\")\n";
  std::string written = Encrypted(RegionWriting(listed));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyDocumenting));
  EXPECT_TRUE(Holds(OpenedBlockWriting(listed), listed));
}

TEST(ProtectCommentDescription, TheCommentStandsImmediatelyPriorToTheBlock) {
  std::string written = Encrypted(RegionWriting(Documents(kNotice)));
  EXPECT_LT(written.find(Documents(kNotice)), written.find(kBlockOpening));
  std::string between = BetweenTheCommentAndTheBlock(written, kNotice);
  EXPECT_EQ(between, "") << written;
  size_t comment_at = written.find(Documents(kNotice));
  ASSERT_GT(comment_at, 1U);
  size_t line_before = written.rfind('\n', comment_at - 2) + 1;
  EXPECT_EQ(written.compare(line_before, kBlockCounting.size(), kBlockCounting),
            0)
      << written;
}

TEST(ProtectCommentDescription, TheCommentFollowsTheKeyBlockOfItsEnvelope) {
  std::string written = Encrypted(RegionBehindAKeyBlock(Documents(kNotice)));
  ASSERT_TRUE(Holds(written, "`pragma protect key_block\n")) << written;
  EXPECT_LT(written.find("`pragma protect key_block\n"),
            written.find(Documents(kNotice)));
  std::string between = BetweenTheCommentAndTheBlock(written, kNotice);
  EXPECT_EQ(TimesWritten(between, kAnyDirective), 0U) << written;
}

TEST(ProtectCommentDescription, TwoCommentsAreOutputInTheOrderWritten) {
  std::string both = Documents(kNotice);
  both.append(Documents(kOtherNotice));
  std::string written = Encrypted(RegionWriting(both));
  EXPECT_LT(written.find(Documents(kNotice)),
            written.find(Documents(kOtherNotice)));
  EXPECT_LT(written.find(Documents(kOtherNotice)), written.find(kBlockOpening));
}

TEST(ProtectCommentDescription, ACommentBesideAnAuthorIsOutputOnItsOwnLine) {
  std::string listed = "`pragma protect author=\"Ada Lovelace\", comment=\"";
  listed.append(kNotice).append("\"\n");
  std::string written = Encrypted(RegionWriting(listed));
  EXPECT_TRUE(Holds(written, Documents(kNotice)));
  EXPECT_TRUE(Holds(written, "`pragma protect author=\"Ada Lovelace\"\n"));
}

TEST(ProtectCommentDescription, AnExpressionBesideTheCommentGoesIntoTheBlock) {
  constexpr std::string_view kLicence =
      "runtime_license=(library=\"lic.so\",entry=\"chk\",feature=\"f\")";
  std::string directive = "`pragma protect comment=\"";
  directive.append(kNotice).append("\", ").append(kLicence).append("\n");
  std::string written = Encrypted(RegionWriting(directive));
  EXPECT_TRUE(Holds(written, Documents(kNotice))) << written;
  EXPECT_FALSE(Holds(written, "runtime_license")) << written;
  EXPECT_TRUE(Holds(OpenedBlockOf(written), kLicence)) << written;
}

TEST(ProtectCommentDescription, TheOpenedBlockHoldsNeitherPragmaNorValue) {
  std::string recovered = OpenedBlockWriting(Documents(kNotice));
  EXPECT_TRUE(Holds(recovered, kSealedDesign));
  EXPECT_FALSE(Holds(recovered, kAnyDocumenting));
  EXPECT_FALSE(Holds(recovered, kNotice));
}

TEST(ProtectCommentDescription, AnEmptyStringCommentIsKeptOutOfTheBlock) {
  std::string recovered = OpenedBlockWriting(Documents(""));
  EXPECT_TRUE(Holds(recovered, kSealedDesign));
  EXPECT_FALSE(Holds(recovered, kAnyDocumenting));
}

TEST(ProtectCommentDescription, TheBlockIsTheOneTheSilentRegionProduces) {
  std::string documented = Encrypted(RegionWriting(Documents(kNotice)));
  std::string silent = Encrypted(RegionWriting(""));
  EXPECT_FALSE(DataBlockOf(silent).empty());
  EXPECT_EQ(DataBlockOf(documented), DataBlockOf(silent));
}

TEST(ProtectCommentDescription, TheKeywordStandingAloneIsLeftInTheBlock) {
  std::string alone = "`pragma protect comment\n";
  EXPECT_FALSE(Holds(Encrypted(RegionWriting(alone)), kAnyDocumenting));
  EXPECT_TRUE(Holds(OpenedBlockWriting(alone), alone));
}

TEST(ProtectCommentDescription, ACommentOutsideEveryRegionIsCopiedInPlace) {
  std::string src = RegionWriting("");
  src.append(Documents(kNotice));
  src.append(RegionWriting(""));
  std::string written = Encrypted(src);
  EXPECT_EQ(TimesWritten(written, kAnyDocumenting), 1U);
  EXPECT_LT(written.find(kEndProtected), written.find(kAnyDocumenting));
  size_t first = written.find(kBeginProtected);
  EXPECT_LT(written.find(kAnyDocumenting),
            written.find(kBeginProtected, first + 1));
}

TEST(ProtectCommentDescription, ACommentInAnUnencryptedFileIsUnchanged) {
  std::string src = "module m;\n";
  src.append(Documents(kNotice));
  src.append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

TEST(ProtectCommentDescription, ARegionReachingNoKeyKeepsItsCommentAsWritten) {
  std::string src = RegionWriting(Documents(kNotice));
  EXPECT_EQ(EncryptedWithoutTheKey(src), src);
}

TEST(ProtectCommentDescription, ACommentInAnEnclosedSealedModelIsNotOutput) {
  std::string enclosed = SealedModelDocumenting(kOtherNotice);
  enclosed.append(ReachesTheKey());
  enclosed.append(Documents(kNotice));
  enclosed.append(kSealedDesign);
  std::string written = Encrypted(RegionAround(enclosed));
  EXPECT_EQ(TimesWritten(written, Documents(kNotice)), 1U);
  EXPECT_FALSE(Holds(written, kOtherNotice));
}

TEST(ProtectCommentDescription,
     ACommentInAnEnclosedSealedModelReachesTheBlock) {
  std::string enclosed = SealedModelDocumenting(kOtherNotice);
  enclosed.append(ReachesTheKey());
  enclosed.append(kSealedDesign);
  std::string recovered = OpenedBlockOf(Encrypted(RegionAround(enclosed)));
  EXPECT_TRUE(Holds(recovered, kBeginProtected));
  EXPECT_TRUE(Holds(recovered, Documents(kOtherNotice)));
}

TEST(ProtectCommentDescription, AnEnvelopeOutputsOnlyItsOwnRegionsComment) {
  std::string second = ReachesTheKey();
  second.append("module other_m; endmodule\n");
  std::string written =
      Encrypted(RegionWriting(Documents(kNotice)) + RegionAround(second));
  EXPECT_EQ(TimesWritten(written, kBeginProtected), 2U);
  EXPECT_EQ(TimesWritten(written, kAnyDocumenting), 1U);
  size_t opened = written.find(kBeginProtected);
  EXPECT_LT(written.find(kAnyDocumenting),
            written.find(kBeginProtected, opened + 1));
}

TEST(ProtectCommentDescription, TheNoticeReachesNoneOfTheRecoveredDesign) {
  ReadWithTheKeys read(Encrypted(RegionWriting(Documents(kNotice))));
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kNotice));
}

TEST(ProtectCommentDescription, TwoEnvelopesDifferingOnlyInTheNoticeReadAlike) {
  std::string one = Encrypted(RegionWriting(Documents(kNotice)));
  std::string other = Encrypted(RegionWriting(Documents(kOtherNotice)));
  ASSERT_NE(one, other);
  ReadWithTheKeys read_one(one);
  ReadWithTheKeys read_other(other);
  EXPECT_FALSE(read_one.diags.HasErrors());
  EXPECT_FALSE(read_other.diags.HasErrors());
  EXPECT_EQ(read_one.produced, read_other.produced);
}

TEST(ProtectCommentDescription, AnEnvelopeCarryingOnlyACommentIsReadAndClosed) {
  std::string envelope(kBeginProtected);
  envelope.append(Documents(kNotice)).append(kEndProtected);
  ReadWithTheKeys read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_EQ(read.Closed(), 1U);
  EXPECT_EQ(read.StillOpen(), 0U);
  EXPECT_FALSE(read.Produced(kNotice));
  EXPECT_TRUE(read.Produced("endmodule"));
}

}  // namespace
