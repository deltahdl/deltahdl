#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "fixture_protect_encoding.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_block.h"

using namespace delta;

struct ProtectDigestBlockSyntaxTest : ::testing::Test {
 protected:
  std::string Preprocess(const std::string& src) {
    auto fid = mgr_.AddFile("<test>", src);
    Preprocessor pp(mgr_, diag_, config_);
    return pp.Preprocess(fid);
  }

  SourceManager mgr_;
  DiagEngine diag_{mgr_};
  PreprocConfig config_;
};

namespace {

TEST_F(ProtectDigestBlockSyntaxTest, PragmaProtectDigestBlockConsumed) {
  auto result = Preprocess("`pragma protect digest_block\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

TEST_F(ProtectDigestBlockSyntaxTest,
       DigestBlockDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect digest_block\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

std::string EnvelopeAnnouncing(std::string_view announced) {
  std::string envelope = EnvelopeAround(kDigestBlockLine);
  size_t at = envelope.find(kDigestBlockLine);
  EXPECT_NE(at, std::string::npos) << envelope;
  std::string rewritten = envelope;
  rewritten.replace(at, kDigestBlockLine.size(), announced);
  return rewritten;
}

struct ReadEnvelope {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, HoldingTheKey()};
  std::string text;

  explicit ReadEnvelope(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectDigestCheck DigestCheck() const { return pp.LastDigestBlockCheck(); }
};

TEST(ProtectDigestBlockSyntax, TheKeywordSpeaksForTheLineBeneathIt) {
  ReadEnvelope run(EnvelopeAround(kDigestBlockLine));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestBlockSyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  ReadEnvelope run(EnvelopeAnnouncing(
      "`pragma protect digest_block=\"a-value-of-its-own\"\n"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kNotChecked);
}

TEST(ProtectDigestBlockSyntax, AListAgainstTheKeywordSpeaksForNoLine) {
  ReadEnvelope run(
      EnvelopeAnnouncing("`pragma protect digest_block=(bytes=\"20\")\n"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kNotChecked);
}

TEST(ProtectDigestBlockSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  ReadEnvelope run(
      EnvelopeAnnouncing("`pragma protect digest_block_of_theirs\n"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kNotChecked);
}

TEST(ProtectDigestBlockSyntax, TheKeywordStandsAloneAmongOtherExpressions) {
  ReadEnvelope run(EnvelopeAnnouncing(
      "`pragma protect comment=\"stands beside it\", digest_block\n"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDigestBlockSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect digest_block =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectDigestBlockSyntax, TheKeywordStandingAloneAsksForADigest) {
  EXPECT_TRUE(Holds(EnvelopeAround(kDigestBlockLine), kDigestBlockLine));
}

TEST(ProtectDigestBlockSyntax, ARegionAskingForNoDigestGetsNone) {
  EXPECT_FALSE(Holds(EnvelopeAround(""), kDigestBlockLine));
}

TEST(ProtectDigestBlockSyntax,
     TheSpellingDecidesWhatIsAnnouncedNotWhatIsAsked) {
  std::string envelope =
      EnvelopeAround("`pragma protect digest_block=\"a-value-of-its-own\"\n");
  EXPECT_TRUE(Holds(envelope, kDigestBlockLine)) << envelope;
}

}  // namespace
