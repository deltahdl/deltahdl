#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_region.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"

using namespace delta;

namespace {

struct EnvelopeRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, {}};

  explicit EnvelopeRun(const std::string& src) {
    pp.Preprocess(mgr.AddFile("<test>", src));
  }

  const ProtectEnvelopeState& Envelopes() const {
    return pp.ProtectEnvelopes();
  }
};

std::string RepeatDirective(const std::string& keyword, size_t count) {
  std::string src;
  for (size_t n = 0; n < count; ++n) {
    src += "`pragma protect " + keyword + "\n";
  }
  return src;
}

TEST(ProtectedEnvelopeOverview, ProtectPragmaOpensEncryptionEnvelope) {
  EnvelopeRun run("`pragma protect begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 1U);
}

TEST(ProtectedEnvelopeOverview, OtherPragmaNameOpensNoEnvelope) {
  EnvelopeRun run(
      "`pragma acme_tool begin\n"
      "`pragma acme_tool begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 0U);
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 0U);
}

TEST(ProtectedEnvelopeOverview, EscapedIdentifierOpensNoEnvelope) {
  EnvelopeRun run("`pragma protect \\begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 0U);
}

TEST(ProtectedEnvelopeOverview, KeywordNestedInsideAValueOpensNoEnvelope) {
  EnvelopeRun run("`pragma protect encoding = ( begin )\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 0U);
}

TEST(ProtectedEnvelopeOverview, EndClosesTheEncryptionEnvelope) {
  EnvelopeRun run("`pragma protect begin\n`pragma protect end\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 0U);
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kEncryption);
}

TEST(ProtectedEnvelopeOverview, EndPairsWithTheMostRecentBegin) {
  EnvelopeRun run(
      "`pragma protect begin\n"
      "`pragma protect begin\n"
      "`pragma protect end\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].begin_loc.line, 2U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].end_loc.line, 3U);
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 1U);
}

TEST(ProtectedEnvelopeOverview, EndWithNothingOpenClosesNoEnvelope) {
  EnvelopeRun run("`pragma protect end\n");
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 0U);
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes().empty());
}

TEST(ProtectedEnvelopeOverview, BeginProtectedOpensADecryptionEnvelope) {
  EnvelopeRun run("`pragma protect begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 1U);
  EXPECT_TRUE(run.Envelopes().InProtectedRegion());
}

TEST(ProtectedEnvelopeOverview, EncryptionEnvelopeDoesNotProtectItsCode) {
  EnvelopeRun run("`pragma protect begin\n");
  EXPECT_FALSE(run.Envelopes().InProtectedRegion());
}

TEST(ProtectedEnvelopeOverview, EndProtectedEndsTheProtectedRegion) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.Envelopes().InProtectedRegion());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kDecryption);
}

TEST(ProtectedEnvelopeOverview, ClosingExpressionsDoNotCrossModes) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect end\n");
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 1U);
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes().empty());
}

TEST(ProtectedEnvelopeOverview, EndProtectedPairsWithTheInnermostOpenEnvelope) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].begin_loc.line, 2U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[1].begin_loc.line, 1U);
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 0U);
}

TEST(ProtectedEnvelopeOverview, EndProtectedWithNothingOpenClosesNoEnvelope) {
  EnvelopeRun run("`pragma protect end_protected\n");
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 0U);
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes().empty());
}

TEST(ProtectedEnvelopeOverview, EncryptionEnvelopeNestsInsideADecryptionOne) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect begin\n"
      "`pragma protect end\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kEncryption);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].begin_loc.line, 2U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[1].mode,
            EnvelopeMode::kDecryption);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[1].begin_loc.line, 1U);
}

TEST(ProtectedEnvelopeOverview, CodeStaysProtectedWhileAnOuterEnvelopeIsOpen) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Envelopes().InProtectedRegion());
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 1U);
}

TEST(ProtectedEnvelopeOverview, NestedEncryptionEnvelopeKeepsCodeProtected) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Envelopes().InProtectedRegion());
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 1U);
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 1U);
}

TEST(ProtectedEnvelopeOverview, EightNestedDecryptionEnvelopesAreProcessed) {
  EnvelopeRun run(RepeatDirective(
      "begin_protected", ProtectEnvelopeState::kMinNestedDecryptionEnvelopes));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(),
            ProtectEnvelopeState::kMinNestedDecryptionEnvelopes);
}

TEST(ProtectedEnvelopeOverview, EightNestedDecryptionEnvelopesAllClose) {
  const size_t kDepth = ProtectEnvelopeState::kMinNestedDecryptionEnvelopes;
  EnvelopeRun run(RepeatDirective("begin_protected", kDepth) +
                  RepeatDirective("end_protected", kDepth));
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), kDepth);
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 0U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().back().begin_loc.line, 1U);
}

TEST(ProtectedEnvelopeOverview, NestingBeyondTheSupportedDepthIsReported) {
  EnvelopeRun run(RepeatDirective(
      "begin_protected",
      ProtectEnvelopeState::kNestedDecryptionEnvelopeLimit + 1));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma nests decryption envelopes more deeply than this "
      "implementation processes",
      static_cast<uint32_t>(
          ProtectEnvelopeState::kNestedDecryptionEnvelopeLimit + 1),
      ""));
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(),
            ProtectEnvelopeState::kNestedDecryptionEnvelopeLimit);
}

TEST(ProtectedEnvelopeOverview, ExpressionsBeforeBeginDescribeTheEnvelope) {
  EnvelopeRun run(
      "`pragma protect data_method = \"aes128-cbc\"\n"
      "`pragma protect begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().OpenEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().OpenEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"data_method"});
  EXPECT_TRUE(run.Envelopes().OpenEnvelopes()[0].content_keywords.empty());
  EXPECT_TRUE(run.Envelopes().PendingEnvelopeKeywords().empty());
}

TEST(ProtectedEnvelopeOverview, ExpressionsInsideAnEnvelopeDescribeItsContent) {
  EnvelopeRun run(
      "`pragma protect begin\n"
      "`pragma protect key_keyname = \"acme-key\"\n"
      "`pragma protect end\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].content_keywords,
            std::vector<std::string>{"key_keyname"});
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes()[0].envelope_keywords.empty());
}

TEST(ProtectedEnvelopeOverview, ExpressionsAfterEndDescribeTheNextEnvelope) {
  EnvelopeRun run(
      "`pragma protect begin\n"
      "`pragma protect end\n"
      "`pragma protect encrypt_agent = \"AcmeCrypt\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().PendingEnvelopeKeywords(),
            std::vector<std::string>{"encrypt_agent"});
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes()[0].content_keywords.empty());
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes()[0].envelope_keywords.empty());
}

TEST(ProtectedEnvelopeOverview, KeywordWithANumberValueTakesTheSameRole) {
  EnvelopeRun run(
      "`pragma protect begin\n"
      "`pragma protect bytes = 4096\n"
      "`pragma protect end\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].content_keywords,
            std::vector<std::string>{"bytes"});
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes()[0].envelope_keywords.empty());
}

TEST(ProtectedEnvelopeOverview, ParenthesizedValueKeywordTakesTheSameRole) {
  EnvelopeRun run(
      "`pragma protect encoding = ( enctype = \"base64\", line_length = 64 )\n"
      "`pragma protect begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().OpenEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().OpenEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"encoding"});
  EXPECT_TRUE(run.Envelopes().OpenEnvelopes()[0].content_keywords.empty());
}

TEST(ProtectedEnvelopeOverview, BeginProtectedSplitsTheSameTwoRoles) {
  EnvelopeRun run(
      "`pragma protect key_keyowner = \"Acme Corp\"\n"
      "`pragma protect begin_protected\n"
      "`pragma protect data_block\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"key_keyowner"});
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].content_keywords,
            std::vector<std::string>{"data_block"});
}

TEST(ProtectedEnvelopeOverview, EachEnvelopeKeepsItsOwnKeywords) {
  EnvelopeRun run(
      "`pragma protect data_method = \"aes128-cbc\"\n"
      "`pragma protect begin\n"
      "`pragma protect key_keyname = \"first-key\"\n"
      "`pragma protect end\n"
      "`pragma protect encrypt_agent = \"AcmeCrypt\"\n"
      "`pragma protect begin_protected\n"
      "`pragma protect data_block\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  const auto& first = run.Envelopes().ClosedEnvelopes()[0];
  const auto& second = run.Envelopes().ClosedEnvelopes()[1];
  EXPECT_EQ(first.envelope_keywords, std::vector<std::string>{"data_method"});
  EXPECT_EQ(first.content_keywords, std::vector<std::string>{"key_keyname"});
  EXPECT_EQ(second.envelope_keywords,
            std::vector<std::string>{"encrypt_agent"});
  EXPECT_EQ(second.content_keywords, std::vector<std::string>{"data_block"});
}

TEST(ProtectedEnvelopeOverview, NestedEnvelopesKeepTheirKeywordsApart) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect key_keyowner = \"Acme Corp\"\n"
      "`pragma protect begin\n"
      "`pragma protect data_keyname = \"inner-region-key\"\n"
      "`pragma protect end\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kEncryption);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].content_keywords,
            std::vector<std::string>{"data_keyname"});
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[1].content_keywords,
            std::vector<std::string>{"key_keyowner"});
}

TEST(ProtectedEnvelopeOverview, ExpressionsOfOneDirectiveAreReadLeftToRight) {
  EnvelopeRun run(
      "`pragma protect encrypt_agent = \"AcmeCrypt\", begin, "
      "key_keyname = \"acme-key\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().OpenEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().OpenEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"encrypt_agent"});
  EXPECT_EQ(run.Envelopes().OpenEnvelopes()[0].content_keywords,
            std::vector<std::string>{"key_keyname"});
}

TEST(ProtectedEnvelopeOverview, SplittingASequenceOverDirectivesKeepsTheRoles) {
  EnvelopeRun run(
      "`pragma protect encrypt_agent = \"AcmeCrypt\"\n"
      "`pragma protect begin\n"
      "`pragma protect key_keyname = \"acme-key\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().OpenEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().OpenEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"encrypt_agent"});
  EXPECT_EQ(run.Envelopes().OpenEnvelopes()[0].content_keywords,
            std::vector<std::string>{"key_keyname"});
}

TEST(ProtectedEnvelopeOverview, SplittingASequenceKeepsThePairing) {
  EnvelopeRun joined("`pragma protect begin, end\n");
  EnvelopeRun split("`pragma protect begin\n`pragma protect end\n");
  EXPECT_EQ(joined.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(split.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(joined.Envelopes().EncryptionEnvelopeDepth(), 0U);
  EXPECT_EQ(split.Envelopes().EncryptionEnvelopeDepth(), 0U);
}

TEST(ProtectEnvelopeEncryptionOrder, TheLaterOfTwoValuesInOneDirectiveStands) {
  std::string later = DesignatesTheProvider();
  later.append("`pragma protect data_keyname=\"no-such-key\", data_keyname=\"");
  later.append(kKeyName).append("\"\n");
  EXPECT_TRUE(
      Holds(Encrypted(later + RegionAround(kSealedDesign)), kBlockOpening));
  std::string earlier = DesignatesTheProvider();
  earlier.append("`pragma protect data_keyname=\"");
  earlier.append(kKeyName).append("\", data_keyname=\"no-such-key\"\n");
  EXPECT_FALSE(
      Holds(Encrypted(earlier + RegionAround(kSealedDesign)), kBlockOpening));
}

TEST(ProtectEnvelopeEncryptionOrder, ANameAfterTheClosingWordIsForWhatFollows) {
  std::string source = ReachesTheKey();
  source.append("`pragma protect begin\n").append(kSealedDesign);
  source.append("`pragma protect end, data_keyname=\"no-such-key\"\n");
  source.append(RegionAround("module next_m; endmodule\n"));
  std::string written = Encrypted(source);
  EXPECT_EQ(TimesWritten(written, kBlockOpening), 1U) << written;
  EXPECT_TRUE(Holds(written, "module next_m; endmodule\n")) << written;
}

}  // namespace
