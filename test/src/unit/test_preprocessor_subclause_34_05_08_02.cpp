#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "helpers_protect_region.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kInputOffering = "assembled in Springfield";

constexpr std::string_view kOtherOffering = "sealed on the night shift";

constexpr std::string_view kAnyOffering = "`pragma protect encrypt_agent_info=";

std::string OffersFurther(std::string_view word) {
  std::string written(kAnyOffering);
  written.append("\"").append(word).append("\"\n");
  return written;
}

std::string TheGeneratedOffering() { return OffersFurther(kEncryptAgentInfo); }

std::string SealedModelOffering(std::string_view word) {
  std::string model = Encrypted(RegionWriting(""));
  std::string offering = TheGeneratedOffering();
  size_t stands = model.find(offering);
  if (stands == std::string::npos) return model;
  model.replace(stands, offering.size(), OffersFurther(word));
  return model;
}

std::string RegionEnclosing(const std::string& model) {
  std::string inside(model);
  inside.append(RegionBody(""));
  return RegionAround(inside);
}

std::string WithTheOfferingReworded(const std::string& envelope,
                                    std::string_view word) {
  std::string offering = TheGeneratedOffering();
  size_t stands = envelope.find(offering);
  if (stands == std::string::npos) return envelope;
  std::string reworded(envelope);
  reworded.replace(stands, offering.size(), OffersFurther(word));
  return reworded;
}

std::string WithTheOfferingMovedPastTheBlock(const std::string& envelope) {
  std::string offering = TheGeneratedOffering();
  size_t stands = envelope.find(offering);
  if (stands == std::string::npos) return envelope;
  std::string moved(envelope);
  moved.erase(stands, offering.size());
  size_t closes = moved.find(kEndProtected);
  if (closes == std::string::npos) return envelope;
  moved.insert(closes, offering);
  return moved;
}

std::string WithTheKeyNameWrittenAsTheOffering(const std::string& envelope) {
  std::string designation = DesignatesTheKey();
  size_t stands = envelope.find(designation);
  if (stands == std::string::npos) return envelope;
  std::string replaced(envelope);
  replaced.replace(stands, designation.size(), OffersFurther(kKeyName));
  return replaced;
}

uint32_t WhereTheOfferedEnvelopesBlockIsWritten(std::string_view envelope) {
  return LineHolding(envelope, kBlockOpening) + 1;
}

std::string OfferingAheadOfTheKeyName() {
  std::string listed = "`pragma protect encrypt_agent_info=\"";
  listed.append(kOtherOffering).append("\", data_keyname=\"");
  listed.append(kKeyName).append("\"\n");
  return listed;
}

std::string OfferingAfterTheKeyName() {
  std::string listed = "`pragma protect data_keyname=\"";
  listed.append(kKeyName).append("\", encrypt_agent_info=\"");
  listed.append(kOtherOffering).append("\"\n");
  return listed;
}

std::string WithTheKeyNameListedAs(const std::string& envelope,
                                   const std::string& listed) {
  std::string designation = DesignatesTheKey();
  size_t stands = envelope.find(designation);
  if (stands == std::string::npos) return envelope;
  std::string replaced(envelope);
  replaced.replace(stands, designation.size(), listed);
  return replaced;
}

TEST(ProtectEncryptAgentInfoDescription, TheWordARegionWroteDescribesNothing) {
  std::string written = Encrypted(RegionWriting(OffersFurther(kInputOffering)));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_FALSE(Holds(written, kInputOffering));
}

TEST(ProtectEncryptAgentInfoDescription, TheBlockRecordsTheRegionsTextEntire) {
  std::string body = RegionBody(OffersFurther(kInputOffering));
  EXPECT_EQ(OpenedBlockOf(Encrypted(RegionAround(body))), body);
}

TEST(ProtectEncryptAgentInfoDescription, AnIdentifierAgainstItIsSealed) {
  std::string offered = "`pragma protect encrypt_agent_info=springfield\n";
  std::string written = Encrypted(RegionWriting(offered));
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_TRUE(Holds(OpenedBlockWriting(offered), offered));
}

TEST(ProtectEncryptAgentInfoDescription, AParenthesizedListAgainstItIsSealed) {
  std::string listed(kAnyOffering);
  listed.append("(site=\"Springfield\", shift=\"2\")\n");
  std::string written = Encrypted(RegionWriting(listed));
  EXPECT_EQ(TimesWritten(written, kAnyOffering), 1U);
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_TRUE(Holds(OpenedBlockWriting(listed), listed));
}

TEST(ProtectEncryptAgentInfoDescription, AnEmptyStringAgainstItIsSealed) {
  std::string offered = OffersFurther("");
  std::string written = Encrypted(RegionWriting(offered));
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_TRUE(Holds(OpenedBlockWriting(offered), offered));
}

TEST(ProtectEncryptAgentInfoDescription, TheKeywordStandingAloneIsSealedToo) {
  std::string bare = "`pragma protect encrypt_agent_info\n";
  std::string written = Encrypted(RegionWriting(bare));
  EXPECT_EQ(TimesWritten(written, kAnyOffering), 1U);
  EXPECT_TRUE(Holds(OpenedBlockWriting(bare), bare));
}

TEST(ProtectEncryptAgentInfoDescription, AWordBesideADesignationIsPassedOver) {
  std::string listed = DesignatesTheProvider();
  listed.append("`pragma protect encrypt_agent_info=\"assembled in ");
  listed.append("Springfield\", ");
  listed.append("data_keyname=\"").append(kKeyName).append("\"\n");
  listed.append(kSealedDesign);
  std::string written = Encrypted(RegionAround(listed));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_FALSE(Holds(written, kInputOffering));
}

TEST(ProtectEncryptAgentInfoDescription, AWordInEffectAheadIsNotDrawnOn) {
  std::string src = OffersFurther(kInputOffering);
  src.append(RegionWriting(""));
  std::string written = Encrypted(src);
  EXPECT_EQ(TimesWritten(written, OffersFurther(kInputOffering)), 1U);
  EXPECT_LT(written.find(OffersFurther(kInputOffering)),
            written.find(kBeginProtected));
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
}

TEST(ProtectEncryptAgentInfoDescription, AWordOutsideEveryRegionIsUntouched) {
  std::string spaced = "`pragma  protect   encrypt_agent_info  =  ";
  spaced.append("\"assembled in Springfield\" // whoever sealed it\n");
  std::string src = "module m;\n";
  src.append(spaced).append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

TEST(ProtectEncryptAgentInfoDescription, AnEnclosedModelsWordIsNotDrawnOn) {
  std::string written =
      Encrypted(RegionEnclosing(SealedModelOffering(kOtherOffering)));
  EXPECT_EQ(TimesWritten(written, kAnyOffering), 1U);
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_FALSE(Holds(written, kOtherOffering));
}

TEST(ProtectEncryptAgentInfoDescription, AnEnclosedModelsWordIsCarriedIn) {
  std::string opened = OpenedBlockOf(
      Encrypted(RegionEnclosing(SealedModelOffering(kOtherOffering))));
  EXPECT_TRUE(Holds(opened, kBeginProtected));
  EXPECT_TRUE(Holds(opened, OffersFurther(kOtherOffering)));
}

TEST(ProtectEncryptAgentInfoDescription, TheProvidedValueIsAStringSayingMore) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_FALSE(kEncryptAgentInfo.empty());
  EXPECT_NE(kEncryptAgentInfo, kEncryptAgent);
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_FALSE(Holds(written, "`pragma protect encrypt_agent_info\n"));
}

TEST(ProtectEncryptAgentInfoDescription, ARegionOfferingNothingStillGetsOne) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_EQ(TimesWritten(written, TheGeneratedOffering()), 1U);
}

TEST(ProtectEncryptAgentInfoDescription, EachEnvelopeIsGivenOneOfItsOwn) {
  std::string second = ReachesTheKey();
  second.append("module other_m; endmodule\n");
  std::string written = Encrypted(RegionWriting("") + RegionAround(second));
  EXPECT_EQ(TimesWritten(written, kBeginProtected), 2U);
  EXPECT_EQ(TimesWritten(written, TheGeneratedOffering()), 2U);
  EXPECT_EQ(TimesWritten(written, kAnyOffering), 2U);
}

TEST(ProtectEncryptAgentInfoDescription, ARegionReachingNoKeyIsGivenNone) {
  std::string src = RegionWriting(OffersFurther(kInputOffering));
  EXPECT_EQ(EncryptedWithoutTheKey(src), src);
}

TEST(ProtectEncryptAgentInfoDescription, NoOfferingIsWrittenWhereNoneIsGiven) {
  std::string with = ProtectEnvelopeDescriptionDirectives(
      {kEncryptAgent, kEncryptAgentInfo, kDataMethod, "(enctype=\"base64\")"});
  std::string without = ProtectEnvelopeDescriptionDirectives(
      {kEncryptAgent, "", kDataMethod, "(enctype=\"base64\")"});
  EXPECT_TRUE(Holds(with, TheGeneratedOffering()));
  EXPECT_FALSE(Holds(without, kAnyOffering));
  EXPECT_TRUE(Holds(without, kDataMethod));
}

TEST(ProtectEncryptAgentInfoDescription, TheOfferingStandsInsideTheEnvelope) {
  std::string written = Encrypted(RegionWriting(""));
  std::string offering = TheGeneratedOffering();
  EXPECT_LT(written.find(kBeginProtected), written.find(offering));
  EXPECT_LT(written.find(offering), written.find(kEndProtected));
}

TEST(ProtectEncryptAgentInfoDescription, TheOfferingStandsAheadOfTheBlock) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_TRUE(Holds(written, kBlockOpening));
  EXPECT_LT(written.find(TheGeneratedOffering()), written.find(kBlockOpening));
}

TEST(ProtectEncryptAgentInfoDescription, TheEnvelopeCarriesTheOnePlaced) {
  std::string written = Encrypted(RegionWriting(OffersFurther(kInputOffering)));
  EXPECT_EQ(TimesWritten(written, kAnyOffering), 1U);
  EXPECT_EQ(TimesWritten(written, TheGeneratedOffering()), 1U);
}

TEST(ProtectEncryptAgentInfoDescription, TheStatedBlockSizeLeavesItOut) {
  std::string body = RegionBody("");
  std::string counted = "bytes=";
  counted.append(std::to_string(ProtectedRegionBlockSize(body))).append(")");
  EXPECT_TRUE(Holds(Encrypted(RegionAround(body)), counted));
}

TEST(ProtectEncryptAgentInfoDescription, OnlyTheProvidedOfferingIsWithheld) {
  std::string written = Encrypted(RegionWriting(OffersFurther(kInputOffering)));
  std::string opened = OpenedBlockOf(written);
  EXPECT_TRUE(Holds(opened, OffersFurther(kInputOffering)));
  EXPECT_FALSE(Holds(opened, kEncryptAgentInfo));
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
}

TEST(ProtectEncryptAgentInfoDescription, ItReachesNoneOfTheRecoveredDesign) {
  ReadWithTheKeys read(Encrypted(RegionWriting("")));
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kEncryptAgentInfo));
}

TEST(ProtectEncryptAgentInfoDescription, TwoEnvelopesDifferingOnlyInItRead) {
  std::string mine = Encrypted(RegionWriting(""));
  std::string theirs = WithTheOfferingReworded(mine, kOtherOffering);
  ASSERT_NE(mine, theirs);
  ReadWithTheKeys read(mine);
  ReadWithTheKeys read_theirs(theirs);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_FALSE(read_theirs.diags.HasErrors());
  EXPECT_EQ(read.produced, read_theirs.produced);
}

TEST(ProtectEncryptAgentInfoDescription, AnOfferingPastTheBlockCostsNothing) {
  std::string moved =
      WithTheOfferingMovedPastTheBlock(Encrypted(RegionWriting("")));
  ASSERT_LT(moved.find(kBlockOpening), moved.find(TheGeneratedOffering()));
  ReadWithTheKeys read(moved);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kEncryptAgentInfo));
}

TEST(ProtectEncryptAgentInfoDescription, AForeignEnvelopeOfferingOnlyItCloses) {
  std::string envelope(kBeginProtected);
  envelope.append(OffersFurther(kOtherOffering)).append(kEndProtected);
  ReadWithTheKeys read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_EQ(read.Closed(), 1U);
  EXPECT_EQ(read.StillOpen(), 0U);
  EXPECT_FALSE(read.Produced(kOtherOffering));
  EXPECT_TRUE(read.Produced("endmodule"));
}

TEST(ProtectEncryptAgentInfoDescription, AnEnclosedModelsWordReachesNoDesign) {
  std::string written =
      Encrypted(RegionEnclosing(SealedModelOffering(kOtherOffering)));
  ReadWithTheKeys read(written);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kOtherOffering));
  EXPECT_FALSE(read.Produced(kEncryptAgentInfo));
}

TEST(ProtectEncryptAgentInfoDescription, AForeignEnvelopeWithTheBareKeyword) {
  std::string envelope(kBeginProtected);
  envelope.append("`pragma protect encrypt_agent_info\n").append(kEndProtected);
  ReadWithTheKeys read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_EQ(read.Closed(), 1U);
  EXPECT_EQ(read.StillOpen(), 0U);
  EXPECT_FALSE(read.Produced("encrypt_agent_info"));
  EXPECT_TRUE(read.Produced("endmodule"));
}

TEST(ProtectEncryptAgentInfoDescription, AnOfferingSpellingAKeyNameOpensNone) {
  std::string replaced =
      WithTheKeyNameWrittenAsTheOffering(Encrypted(RegionWriting("")));
  ASSERT_TRUE(Holds(replaced, OffersFurther(kKeyName)));
  ReadWithTheKeys read(replaced);
  EXPECT_TRUE(ReportedError(
      read.diags.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      WhereTheOfferedEnvelopesBlockIsWritten(replaced), "34.3.2"));
  EXPECT_FALSE(read.Produced("module sealed_m"));
}

TEST(ProtectEncryptAgentInfoDescription, AnOfferingAheadOfTheKeyNameCostsNone) {
  std::string listed = OfferingAheadOfTheKeyName();
  std::string rewritten =
      WithTheKeyNameListedAs(Encrypted(RegionWriting("")), listed);
  ASSERT_TRUE(Holds(rewritten, listed));
  ReadWithTheKeys read(rewritten);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kOtherOffering));
}

TEST(ProtectEncryptAgentInfoDescription, AnOfferingAfterTheKeyNameCostsNone) {
  std::string listed = OfferingAfterTheKeyName();
  std::string rewritten =
      WithTheKeyNameListedAs(Encrypted(RegionWriting("")), listed);
  ASSERT_TRUE(Holds(rewritten, listed));
  ReadWithTheKeys read(rewritten);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kOtherOffering));
}

}  // namespace
