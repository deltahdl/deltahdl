#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
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

constexpr std::string_view kLicenseLine =
    "`pragma protect runtime_license=(library=\"lic.so\", entry=\"acquire\", "
    "feature=\"simulate\")\n";

constexpr std::string_view kAuthorLine =
    "`pragma protect author=\"Acme Corp\"\n";

TEST(ProtectedEnvelopeOverview, EndClosesTheOnlyOpenBeginAndSealsItsText) {
  std::string written =
      Encrypted(ReachesTheKey() + RegionAround(kSealedDesign));
  EXPECT_EQ(TimesWritten(written, kBeginProtected), 1U) << written;
  EXPECT_EQ(TimesWritten(written, kEndProtected), 1U) << written;
  EXPECT_FALSE(Holds(written, kSealedDesign)) << written;
  EXPECT_EQ(OpenedBlockOf(written), std::string(kSealedDesign));
}

TEST(ProtectedEnvelopeOverview,
     EndWithNothingOpenIsNotReportedAndSealsNothing) {
  const std::string kLoose = "`pragma protect end\nmodule loose_m; endmodule\n";
  EnvelopeRun run(kLoose);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 0U);
  std::string written = Encrypted(ReachesTheKey() + kLoose);
  EXPECT_FALSE(Holds(written, kBeginProtected)) << written;
  EXPECT_TRUE(Holds(written, "module loose_m; endmodule\n")) << written;
}

TEST(ProtectedEnvelopeOverview, EndLeavesAnOpenDecryptionEnvelopeProtecting) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect end\n");
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 0U);
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 1U);
  EXPECT_TRUE(run.Envelopes().InProtectedRegion());
}

TEST(ProtectedEnvelopeOverview,
     DISABLED_BeginAndEndInOneDirectiveSealAsWhenSplit) {
  std::string joined =
      Encrypted(ReachesTheKey() + "`pragma protect begin, end\n");
  std::string split = Encrypted(ReachesTheKey() +
                                "`pragma protect begin\n`pragma protect end\n");
  EXPECT_EQ(TimesWritten(joined, kBeginProtected), 1U) << joined;
  EXPECT_EQ(TimesWritten(split, kBeginProtected), 1U) << split;
  EXPECT_EQ(DataBlockOf(joined), DataBlockOf(split));
  EXPECT_FALSE(DataBlockOf(joined).empty());
}

TEST(ProtectedEnvelopeOverview, EndProtectedLeavesAnOpenBeginOpen) {
  EnvelopeRun open(
      "`pragma protect begin\n"
      "`pragma protect end_protected\n");
  EXPECT_EQ(open.Envelopes().EncryptionEnvelopeDepth(), 1U);
  EXPECT_EQ(open.Envelopes().DecryptionEnvelopeDepth(), 0U);
  EXPECT_FALSE(open.Envelopes().InProtectedRegion());
  EnvelopeRun closed(
      "`pragma protect begin\n"
      "`pragma protect end_protected\n"
      "`pragma protect end\n");
  EXPECT_EQ(closed.Envelopes().EncryptionEnvelopeDepth(), 0U);
}

TEST(ProtectedEnvelopeOverview, InnerEncryptionEnvelopeClosesBeforeTheOuter) {
  EnvelopeRun inner_closed(
      "`pragma protect begin_protected\n"
      "`pragma protect begin\n"
      "`pragma protect end\n");
  EXPECT_FALSE(inner_closed.diag.HasErrors());
  EXPECT_EQ(inner_closed.Envelopes().EncryptionEnvelopeDepth(), 0U);
  EXPECT_EQ(inner_closed.Envelopes().DecryptionEnvelopeDepth(), 1U);
  EXPECT_TRUE(inner_closed.Envelopes().InProtectedRegion());
  EnvelopeRun both_closed(
      "`pragma protect begin_protected\n"
      "`pragma protect begin\n"
      "`pragma protect end\n"
      "`pragma protect end_protected\n");
  EXPECT_EQ(both_closed.Envelopes().DecryptionEnvelopeDepth(), 0U);
  EXPECT_FALSE(both_closed.Envelopes().InProtectedRegion());
}

TEST(ProtectedEnvelopeOverview,
     BeginProtectedAndEndProtectedInOneDirectivePair) {
  EnvelopeRun joined("`pragma protect begin_protected, end_protected\n");
  EnvelopeRun split(
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(joined.diag.HasErrors());
  EXPECT_EQ(joined.Envelopes().DecryptionEnvelopeDepth(), 0U);
  EXPECT_EQ(split.Envelopes().DecryptionEnvelopeDepth(), 0U);
  EXPECT_FALSE(joined.Envelopes().InProtectedRegion());
}

TEST(ProtectedEnvelopeOverview,
     ExpressionBeforeBeginIsCarriedAheadOfTheEnvelope) {
  std::string written = Encrypted(ReachesTheKey() + std::string(kAuthorLine) +
                                  RegionAround(kSealedDesign));
  ASSERT_TRUE(Holds(written, kAuthorLine)) << written;
  EXPECT_LT(written.find(kAuthorLine), written.find(kBeginProtected));
  EXPECT_EQ(OpenedBlockOf(written), std::string(kSealedDesign));
}

std::string OneDirectiveSequence() {
  std::string src = ReachesTheKey();
  src.append("`pragma protect author=\"Acme Corp\", begin, ");
  src.append(kLicenseLine.substr(std::string_view("`pragma protect ").size()));
  src.append(kSealedDesign).append("`pragma protect end\n");
  return src;
}

std::string SplitSequence() {
  std::string src = ReachesTheKey();
  src.append(kAuthorLine).append("`pragma protect begin\n");
  src.append(kLicenseLine).append(kSealedDesign);
  src.append("`pragma protect end\n");
  return src;
}

void ExpectAuthorDescribesAndLicenseIsSealed(const std::string& written) {
  EXPECT_LT(written.find("author=\"Acme Corp\""),
            written.find("begin_protected"))
      << written;
  EXPECT_FALSE(Holds(written, "runtime_license")) << written;
  EXPECT_TRUE(Holds(OpenedBlockOf(written), "runtime_license=(")) << written;
  EXPECT_TRUE(Holds(OpenedBlockOf(written), kSealedDesign)) << written;
}

TEST(ProtectedEnvelopeOverview, OneDirectiveSequenceSealsLeftToRight) {
  ExpectAuthorDescribesAndLicenseIsSealed(Encrypted(OneDirectiveSequence()));
}

TEST(ProtectedEnvelopeOverview, SplitSequenceSealsAsTheOneDirectiveDoes) {
  ExpectAuthorDescribesAndLicenseIsSealed(Encrypted(SplitSequence()));
}

TEST(ProtectedEnvelopeOverview, ExpressionAfterEndProtectedLeavesTheClosedOne) {
  std::string envelope =
      Encrypted(ReachesTheKey() + RegionAround(kSealedDesign));
  ReadWithTheKeys read(envelope +
                       "`pragma protect data_method=\"no-such-method\"\n");
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced(kSealedDesign)) << read.produced;
  EXPECT_EQ(read.StillOpen(), 0U);
}

std::string ReadingKeyNamedTwice(std::string_view first,
                                 std::string_view second) {
  std::string envelope =
      Encrypted(ReachesTheKey() + RegionAround(kSealedDesign));
  std::string named = "data_keyname=\"";
  named.append(kKeyName).append("\"");
  size_t at = envelope.find(named, envelope.find(kBeginProtected));
  if (at == std::string::npos) return {};
  std::string twice = "data_keyname=\"";
  twice.append(first).append("\", data_keyname=\"").append(second);
  twice.append("\"");
  return envelope.replace(at, named.size(), twice);
}

TEST(ProtectedEnvelopeOverview, DISABLED_LaterOfTwoValuesStandsWhenReading) {
  std::string later = ReadingKeyNamedTwice("no-such-key", kKeyName);
  ASSERT_FALSE(later.empty());
  ReadWithTheKeys right(later);
  EXPECT_FALSE(right.diags.HasErrors());
  EXPECT_TRUE(right.Produced(kSealedDesign)) << right.produced;
  ReadWithTheKeys wrong(ReadingKeyNamedTwice(kKeyName, "no-such-key"));
  EXPECT_TRUE(ReportedError(wrong.diags.Diagnostics(),
                            "protect pragma data_keyname names no key held by "
                            "the data_keyowner in effect",
                            9, "34.5.12"));
  EXPECT_FALSE(wrong.Produced(kSealedDesign)) << wrong.produced;
}

}  // namespace
