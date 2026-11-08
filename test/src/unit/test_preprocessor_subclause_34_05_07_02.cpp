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
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kInputAgent = "AcmeCrypt 3.1";

constexpr std::string_view kOtherAgent = "Globex Sealer 7";

constexpr std::string_view kAnyNaming = "`pragma protect encrypt_agent=";

std::string NamesTheAgent(std::string_view name) {
  std::string written = "`pragma protect encrypt_agent=\"";
  written.append(name).append("\"\n");
  return written;
}

std::string TheGeneratedNaming() { return NamesTheAgent(kEncryptAgent); }

std::string SealedModelNaming(std::string_view name) {
  std::string model = Encrypted(RegionWriting(""));
  std::string naming = TheGeneratedNaming();
  size_t stands = model.find(naming);
  if (stands == std::string::npos) return model;
  model.replace(stands, naming.size(), NamesTheAgent(name));
  return model;
}

std::string RegionEnclosingSealedModel(std::string_view sealed) {
  std::string inside(sealed);
  inside.append(ReachesTheKey()).append(kSealedDesign);
  return RegionAround(inside);
}

std::string WithTheAgentRenamed(const std::string& envelope,
                                std::string_view name) {
  std::string naming = TheGeneratedNaming();
  size_t stands = envelope.find(naming);
  if (stands == std::string::npos) return envelope;
  std::string renamed(envelope);
  renamed.replace(stands, naming.size(), NamesTheAgent(name));
  return renamed;
}

std::string WithTheNamingMovedPastTheBlock(const std::string& envelope) {
  std::string naming = TheGeneratedNaming();
  size_t stands = envelope.find(naming);
  if (stands == std::string::npos) return envelope;
  std::string moved(envelope);
  moved.erase(stands, naming.size());
  size_t closes = moved.find(kEndProtected);
  if (closes == std::string::npos) return envelope;
  moved.insert(closes, naming);
  return moved;
}

std::string WithTheKeyNameWrittenAsTheNaming(const std::string& envelope) {
  std::string designation = DesignatesTheKey();
  size_t stands = envelope.find(designation);
  if (stands == std::string::npos) return envelope;
  std::string replaced(envelope);
  replaced.replace(stands, designation.size(), NamesTheAgent(kKeyName));
  return replaced;
}

uint32_t TheSealedBlocksLine(std::string_view envelope) {
  return LineHolding(envelope, kBlockOpening) + 1;
}

TEST(ProtectEncryptAgentDescription, TheNameARegionWroteDescribesNoEnvelope) {
  std::string written = Encrypted(RegionWriting(NamesTheAgent(kInputAgent)));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_FALSE(Holds(written, kInputAgent));
}

TEST(ProtectEncryptAgentDescription, TheBlockRecordsTheRegionsTextEntire) {
  std::string body = RegionBody(NamesTheAgent(kInputAgent));
  EXPECT_EQ(OpenedBlockOf(Encrypted(RegionAround(body))), body);
}

TEST(ProtectEncryptAgentDescription, AnIdentifierAgainstTheKeywordIsSealed) {
  std::string named = "`pragma protect encrypt_agent=acme_crypt\n";
  std::string written = Encrypted(RegionWriting(named));
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_TRUE(Holds(OpenedBlockWriting(named), named));
}

TEST(ProtectEncryptAgentDescription, AParenthesizedListAgainstItIsSealed) {
  std::string listed =
      "`pragma protect encrypt_agent=(name=\"Acme\", version=\"3.1\")\n";
  std::string written = Encrypted(RegionWriting(listed));
  EXPECT_EQ(TimesWritten(written, kAnyNaming), 1U);
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_TRUE(Holds(OpenedBlockWriting(listed), listed));
}

TEST(ProtectEncryptAgentDescription, AnEmptyStringAgainstTheKeywordIsSealed) {
  std::string named = NamesTheAgent("");
  std::string written = Encrypted(RegionWriting(named));
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_TRUE(Holds(OpenedBlockWriting(named), named));
}

TEST(ProtectEncryptAgentDescription, TheKeywordStandingAloneIsSealedToo) {
  std::string bare = "`pragma protect encrypt_agent\n";
  std::string written = Encrypted(RegionWriting(bare));
  EXPECT_EQ(TimesWritten(written, kAnyNaming), 1U);
  EXPECT_TRUE(Holds(OpenedBlockWriting(bare), bare));
}

TEST(ProtectEncryptAgentDescription, ANameBesideAKeyDesignationIsPassedOver) {
  std::string listed = DesignatesTheProvider();
  listed.append("`pragma protect encrypt_agent=\"AcmeCrypt 3.1\", ");
  listed.append("data_keyname=\"").append(kKeyName).append("\"\n");
  listed.append(kSealedDesign);
  std::string written = Encrypted(RegionAround(listed));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_FALSE(Holds(written, kInputAgent));
}

TEST(ProtectEncryptAgentDescription, ANameInEffectAheadOfARegionIsNotDrawnOn) {
  std::string src = NamesTheAgent(kInputAgent);
  src.append(RegionWriting(""));
  std::string written = Encrypted(src);
  EXPECT_EQ(TimesWritten(written, NamesTheAgent(kInputAgent)), 1U);
  EXPECT_LT(written.find(NamesTheAgent(kInputAgent)),
            written.find(kBeginProtected));
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
}

TEST(ProtectEncryptAgentDescription, ANameOutsideEveryRegionStaysAsWritten) {
  std::string spaced = "`pragma  protect   encrypt_agent  =  ";
  spaced.append("\"AcmeCrypt 3.1\" // whoever sealed it\n");
  std::string src = "module m;\n";
  src.append(spaced).append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

TEST(ProtectEncryptAgentDescription, AnEnclosedSealedModelsNameIsNotDrawnOn) {
  std::string written =
      Encrypted(RegionEnclosingSealedModel(SealedModelNaming(kOtherAgent)));
  EXPECT_EQ(TimesWritten(written, kAnyNaming), 1U);
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_FALSE(Holds(written, kOtherAgent));
}

TEST(ProtectEncryptAgentDescription, AnEnclosedSealedModelsNameIsCarriedIn) {
  std::string opened = OpenedBlockOf(
      Encrypted(RegionEnclosingSealedModel(SealedModelNaming(kOtherAgent))));
  EXPECT_TRUE(Holds(opened, kBeginProtected));
  EXPECT_TRUE(Holds(opened, NamesTheAgent(kOtherAgent)));
}

TEST(ProtectEncryptAgentDescription, TheGeneratedValueIsAStringNamingATool) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_FALSE(kEncryptAgent.empty());
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_FALSE(Holds(written, "`pragma protect encrypt_agent\n"));
}

TEST(ProtectEncryptAgentDescription, ARegionNamingNoToolStillGetsANaming) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_EQ(TimesWritten(written, TheGeneratedNaming()), 1U);
}

TEST(ProtectEncryptAgentDescription, EachEnvelopeIsGivenANamingOfItsOwn) {
  std::string second = ReachesTheKey();
  second.append("module other_m; endmodule\n");
  std::string written = Encrypted(RegionWriting("") + RegionAround(second));
  EXPECT_EQ(TimesWritten(written, kBeginProtected), 2U);
  EXPECT_EQ(TimesWritten(written, TheGeneratedNaming()), 2U);
  EXPECT_EQ(TimesWritten(written, kAnyNaming), 2U);
}

TEST(ProtectEncryptAgentDescription, ARegionReachingNoKeyIsGivenNoNaming) {
  std::string src = RegionWriting(NamesTheAgent(kInputAgent));
  EXPECT_EQ(EncryptedWithoutTheKey(src), src);
}

TEST(ProtectEncryptAgentDescription, TheNamingStandsInsideTheEnvelope) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_LT(written.find(kBeginProtected), written.find(TheGeneratedNaming()));
  EXPECT_LT(written.find(TheGeneratedNaming()), written.find(kEndProtected));
}

TEST(ProtectEncryptAgentDescription, TheNamingStandsAheadOfTheBlock) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_TRUE(Holds(written, kBlockOpening));
  EXPECT_LT(written.find(TheGeneratedNaming()), written.find(kBlockOpening));
}

TEST(ProtectEncryptAgentDescription, TheEnvelopeCarriesTheOneNamingPlaced) {
  std::string written = Encrypted(RegionWriting(NamesTheAgent(kInputAgent)));
  EXPECT_EQ(TimesWritten(written, kAnyNaming), 1U);
  EXPECT_EQ(TimesWritten(written, TheGeneratedNaming()), 1U);
}

TEST(ProtectEncryptAgentDescription, TheStatedBlockSizeLeavesTheNamingOut) {
  std::string body = RegionBody("");
  std::string counted = "bytes=";
  counted.append(std::to_string(ProtectedRegionBlockSize(body))).append(")");
  EXPECT_TRUE(Holds(Encrypted(RegionAround(body)), counted));
}

TEST(ProtectEncryptAgentDescription, OnlyTheGeneratedNamingIsWithheld) {
  std::string written = Encrypted(RegionWriting(NamesTheAgent(kInputAgent)));
  std::string opened = OpenedBlockOf(written);
  EXPECT_TRUE(Holds(opened, NamesTheAgent(kInputAgent)));
  EXPECT_FALSE(Holds(opened, kEncryptAgent));
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
}

TEST(ProtectEncryptAgentDescription, TheNamingReachesNoneOfTheRecoveredDesign) {
  ReadWithTheKeys read(Encrypted(RegionWriting("")));
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kEncryptAgent));
}

TEST(ProtectEncryptAgentDescription, TwoEnvelopesDifferingOnlyInTheNameRead) {
  std::string mine = Encrypted(RegionWriting(""));
  std::string theirs = WithTheAgentRenamed(mine, kOtherAgent);
  ASSERT_NE(mine, theirs);
  ReadWithTheKeys read(mine);
  ReadWithTheKeys read_theirs(theirs);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_FALSE(read_theirs.diags.HasErrors());
  EXPECT_EQ(read.produced, read_theirs.produced);
}

TEST(ProtectEncryptAgentDescription, ANamingPastTheBlockCostsTheReadingNone) {
  std::string moved =
      WithTheNamingMovedPastTheBlock(Encrypted(RegionWriting("")));
  ASSERT_LT(moved.find(kBlockOpening), moved.find(TheGeneratedNaming()));
  ReadWithTheKeys read(moved);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kEncryptAgent));
}

TEST(ProtectEncryptAgentDescription, AForeignEnvelopeNamingOnlyAToolIsClosed) {
  std::string envelope(kBeginProtected);
  envelope.append(NamesTheAgent(kOtherAgent)).append(kEndProtected);
  ReadWithTheKeys read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_EQ(read.Closed(), 1U);
  EXPECT_EQ(read.StillOpen(), 0U);
  EXPECT_FALSE(read.Produced(kOtherAgent));
  EXPECT_TRUE(read.Produced("endmodule"));
}

TEST(ProtectEncryptAgentDescription, AnEnclosedModelsNameReachesNoDesignText) {
  std::string written =
      Encrypted(RegionEnclosingSealedModel(SealedModelNaming(kOtherAgent)));
  ReadWithTheKeys read(written);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kOtherAgent));
  EXPECT_FALSE(read.Produced(kEncryptAgent));
}

TEST(ProtectEncryptAgentDescription, AForeignEnvelopeWithTheBareKeywordIsRead) {
  std::string envelope(kBeginProtected);
  envelope.append("`pragma protect encrypt_agent\n").append(kEndProtected);
  ReadWithTheKeys read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_EQ(read.Closed(), 1U);
  EXPECT_EQ(read.StillOpen(), 0U);
  EXPECT_FALSE(read.Produced("encrypt_agent"));
  EXPECT_TRUE(read.Produced("endmodule"));
}

TEST(ProtectEncryptAgentDescription, ANamingSpellingAKeyNameOpensNothing) {
  std::string replaced =
      WithTheKeyNameWrittenAsTheNaming(Encrypted(RegionWriting("")));
  ASSERT_TRUE(Holds(replaced, NamesTheAgent(kKeyName)));
  ReadWithTheKeys read(replaced);
  EXPECT_TRUE(ReportedError(
      read.diags.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      TheSealedBlocksLine(replaced), "34.3.2"));
  EXPECT_FALSE(read.Produced("module sealed_m"));
}

}  // namespace
