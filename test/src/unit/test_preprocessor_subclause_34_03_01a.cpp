#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kExchangeKey = "acme-exchange-key";
constexpr std::string_view kOtherKey = "not-the-authors-key";

std::string Encrypted(std::string_view src) {
  return EncryptEnvelopes(src, kExchangeKey);
}

constexpr std::string_view kSpecifiedEnvelope =
    "`pragma protect data_method=\"x-caesar\", "
    "data_keyname=\"rot13\", begin\n"
    "  initial result = 42;\n"
    "`pragma protect end\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

constexpr std::string_view kRecordedBlockOpening =
    "`pragma protect data_block\n";

std::vector<std::string> RecordedBlocks(std::string_view text) {
  std::vector<std::string> blocks;
  size_t pos = text.find(kRecordedBlockOpening);
  while (pos != std::string_view::npos) {
    size_t start = pos + kRecordedBlockOpening.size();
    size_t close = text.find('\n', start);
    if (close == std::string_view::npos) close = text.size();
    blocks.emplace_back(text.substr(start, close - start));
    pos = text.find(kRecordedBlockOpening, close);
  }
  return blocks;
}

std::string Recovered(const std::string& block, std::string_view key) {
  std::string cleartext;
  if (!DecryptProtectedRegion(block, key, &cleartext)) return "";
  return cleartext;
}

bool Recoverable(const std::string& block, std::string_view key) {
  std::string cleartext;
  return DecryptProtectedRegion(block, key, &cleartext);
}

std::string OneBlock(std::string_view src) {
  std::vector<std::string> blocks = RecordedBlocks(Encrypted(src));
  return blocks.empty() ? "" : blocks.front();
}

struct ReadBack {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;
  ProtectedEnvelope envelope{};

  explicit ReadBack(const std::string& src) : pp(mgr, diag, KeyConfig()) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
    if (!pp.ProtectEnvelopes().ClosedEnvelopes().empty()) {
      envelope = pp.ProtectEnvelopes().ClosedEnvelopes().front();
    }
  }

  static PreprocConfig KeyConfig() {
    PreprocConfig config;
    config.protect_key = kExchangeKey;
    return config;
  }
};

bool Names(const std::vector<std::string>& keywords, std::string_view keyword) {
  for (const std::string& name : keywords) {
    if (name == keyword) return true;
  }
  return false;
}

TEST(EnvelopeEncryption, SpecifyingExpressionsAreCarriedOntoTheNewEnvelope) {
  std::string opening =
      "`pragma protect data_method=\"x-caesar\", "
      "data_keyname=\"rot13\", begin_protected\n";
  std::string written = Encrypted(kSpecifiedEnvelope);
  EXPECT_TRUE(Holds(written, opening));
  EXPECT_FALSE(Holds(written, "begin\n"));
}

TEST(EnvelopeEncryption, CarriedExpressionsSpecifyTheDecryptionEnvelope) {
  ReadBack run(Encrypted(kSpecifiedEnvelope));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Names(run.envelope.envelope_keywords, "data_method"));
  EXPECT_TRUE(Names(run.envelope.envelope_keywords, "data_keyname"));
}

TEST(EnvelopeEncryption, TheRecordedBlockIsAContentExpressionOfTheEnvelope) {
  std::string src =
      "`pragma protect data_method=\"x-caesar\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  ReadBack run(Encrypted(src));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Names(run.envelope.content_keywords, "data_block"));
  EXPECT_FALSE(Names(run.envelope.envelope_keywords, "data_block"));
}

TEST(EnvelopeEncryption, EachEnvelopeKeepsTheExpressionsThatSpecifiedIt) {
  std::string written = Encrypted(
      "`pragma protect author=\"Acme Corp\", begin\n"
      "  initial first = 1;\n"
      "`pragma protect end\n"
      "`pragma protect author_info=\"second team\", begin\n"
      "  initial second = 2;\n"
      "`pragma protect end\n");
  std::string first_opening =
      "`pragma protect author=\"Acme Corp\", begin_protected\n";
  std::string second_opening =
      "`pragma protect author_info=\"second team\", begin_protected\n";
  EXPECT_TRUE(Holds(written, first_opening));
  EXPECT_TRUE(Holds(written, second_opening));
  EXPECT_FALSE(Holds(written, "author=\"Acme Corp\", author_info="));
}

TEST(EnvelopeEncryption, AnExpressionBesideTheClosingDelimiterStaysInside) {
  std::string src =
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect comment=\"end of the region\", end\n";
  ReadBack run(Encrypted(src));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Names(run.envelope.content_keywords, "comment"));
  EXPECT_FALSE(Names(run.envelope.envelope_keywords, "comment"));
}

TEST(EnvelopeEncryption, AnExpressionOnItsOwnDirectiveStillSpecifies) {
  std::string src =
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  ReadBack run(Encrypted(src));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Names(run.envelope.envelope_keywords, "author"));
}

TEST(EnvelopeEncryption, TheDescriptionWrittenWithTheBlockGovernsIt) {
  ReadBack run(Encrypted(kSpecifiedEnvelope));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Names(run.envelope.envelope_keywords, "data_method"));
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
}

TEST(EnvelopeEncryption, ACommentOnADelimiterIsNotACarriedExpression) {
  std::string opening =
      "`pragma protect author=\"Acme Corp\", begin_protected\n";
  std::string src =
      "`pragma protect author=\"Acme Corp\", begin /* a note */\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  std::string written = Encrypted(src);
  ReadBack run(written);
  EXPECT_TRUE(Holds(written, opening));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Names(run.envelope.envelope_keywords, "author"));
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
}

TEST(EnvelopeEncryption, ADelimiterStandingAloneIsCarriedAlone) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(written, "`pragma protect begin_protected\n"));
  EXPECT_TRUE(Holds(written, "`pragma protect end_protected\n"));
}

TEST(EnvelopeEncryption, AnExpressionInsideTheEnvelopeIsEncryptedWithIt) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "`pragma protect runtime_license=(library=\"lic.so\", "
      "entry=\"acquire\", feature=\"simulate\")\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_FALSE(Holds(written, "runtime_license"));
  ASSERT_EQ(RecordedBlocks(written).size(), 1U);
  EXPECT_EQ(Recovered(RecordedBlocks(written)[0], kExchangeKey),
            "`pragma protect runtime_license=(library=\"lic.so\", "
            "entry=\"acquire\", feature=\"simulate\")\n"
            "  initial result = 42;\n");
}

TEST(EnvelopeEncryption, TheSameExpressionOutsideTheEnvelopeIsNotEncrypted) {
  std::string written = Encrypted(
      "`pragma protect runtime_license=(library=\"lic.so\", "
      "entry=\"acquire\", feature=\"simulate\")\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(written,
                    "runtime_license=(library=\"lic.so\", entry=\"acquire\", "
                    "feature=\"simulate\")\n"));
  ASSERT_EQ(RecordedBlocks(written).size(), 1U);
  EXPECT_EQ(Recovered(RecordedBlocks(written)[0], kExchangeKey),
            "  initial result = 42;\n");
}

TEST(EnvelopeEncryption, AnEnvelopeEnclosingNoTextIsStillReplaced) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "`pragma protect end\n");
  std::vector<std::string> blocks = RecordedBlocks(written);
  ASSERT_EQ(blocks.size(), 1U);
  EXPECT_TRUE(Recoverable(blocks.front(), kExchangeKey));
  EXPECT_EQ(Recovered(blocks.front(), kExchangeKey), "");
}

TEST(EnvelopeEncryption, ABodyThatIsNotSystemVerilogIsEncryptedUnread) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "?? not a design at all ((\n"
      "\"no closing quote\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedBlocks(written).size(), 1U);
  EXPECT_EQ(Recovered(RecordedBlocks(written)[0], kExchangeKey),
            "?? not a design at all ((\n"
            "\"no closing quote\n");
}

TEST(EnvelopeEncryption, ATextWithNoEnvelopeIsCarriedAcrossWhole) {
  std::string src =
      "module secret (a, b);\n"
      "`pragma protect author=\"Acme Corp\"\n"
      "  initial result = 42;\n"
      "endmodule\n";
  EXPECT_EQ(Encrypted(src), src);
  EXPECT_TRUE(RecordedBlocks(Encrypted(src)).empty());
}

TEST(EnvelopeEncryption, TextBetweenTwoEnvelopesBelongsToNeither) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial first = 1;\n"
      "`pragma protect end\n"
      "  initial between = 2;\n"
      "`pragma protect begin\n"
      "  initial second = 3;\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedBlocks(written).size(), 2U);
  EXPECT_TRUE(Holds(written, "  initial between = 2;\n"));
  EXPECT_EQ(Recovered(RecordedBlocks(written)[0], kExchangeKey),
            "  initial first = 1;\n");
  EXPECT_EQ(Recovered(RecordedBlocks(written)[1], kExchangeKey),
            "  initial second = 3;\n");
}

TEST(EnvelopeEncryption, TextOutsideAnEnvelopeIsCarriedAcrossByteForByte) {
  std::string unchanged =
      "module secret (a, b);\n"
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect begin_protected\n";
  std::string written = Encrypted(
      "module secret (a, b);\n"
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_TRUE(Holds(written, unchanged));
  EXPECT_TRUE(Holds(written, "endmodule\n"));
}

TEST(EnvelopeEncryption, TheDelimitingDirectivesThemselvesAreModified) {
  std::string src =
      "module secret (a, b);\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n";
  EXPECT_NE(Encrypted(src), src);
  EXPECT_FALSE(Holds(Encrypted(src), "`pragma protect begin\n"));
  EXPECT_FALSE(Holds(Encrypted(src), "`pragma protect end\n"));
}

TEST(EnvelopeEncryption, AnUnclosedDelimiterLeavesTheTextAsItWasWritten) {
  std::string src =
      "module secret (a, b);\n"
      "`pragma protect data_method=\"x-caesar\", begin\n"
      "  initial result = 42;\n";
  EXPECT_EQ(Encrypted(src), src);
  EXPECT_TRUE(RecordedBlocks(Encrypted(src)).empty());
}

TEST(EnvelopeEncryption, TheRegionIsRecordedUnderTheExchangeKeyAlone) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedBlocks(written).size(), 1U);
  EXPECT_FALSE(Holds(written, "key_block"));
  EXPECT_EQ(Recovered(RecordedBlocks(written)[0], kExchangeKey),
            "  initial result = 42;\n");
}

TEST(EnvelopeEncryption, ASecondKeyOpensNothingTheExchangeKeyEncrypted) {
  std::string block = OneBlock(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_FALSE(Recoverable(block, kOtherKey));
  EXPECT_EQ(Recovered(block, kOtherKey), "");
}

TEST(EnvelopeEncryption, NoKeyToEncryptUnderLeavesTheTextAsItStands) {
  std::string src =
      "module secret (a, b);\n"
      "`pragma protect data_method=\"x-caesar\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n";
  EXPECT_EQ(EncryptEnvelopes(src, ""), src);
  EXPECT_TRUE(RecordedBlocks(EncryptEnvelopes(src, "")).empty());
}

TEST(EnvelopeEncryption, AnEnvelopeFormedHereOpensAgainUnderTheSameKey) {
  ReadBack run(Encrypted(kSpecifiedEnvelope));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
  EXPECT_FALSE(Holds(run.text, "data_block"));
}

TEST(EnvelopeEncryption, ARegionWithNoKeyIsReportedWhereItOpens) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  const std::string kSource =
      "module m;\n"
      "`pragma protect begin\n"
      "  initial x = 1;\n"
      "`pragma protect end\n"
      "endmodule\n";
  std::string out = EncryptEnvelopes(kSource, "", ProtectKeyList(), &diag,
                                     mgr.AddFile("<test>", kSource));
  EXPECT_EQ(out, kSource);
  EXPECT_TRUE(ReportedError(diag.Diagnostics(),
                            "protect pragma encryption envelope has no key to "
                            "be encrypted under, so it is written out "
                            "unencrypted",
                            2, "34.3.1"));
}

TEST(EnvelopeEncryption, TheKeywordScopeCarriesFromOneTextToTheNext) {
  ProtectKeyList keys;
  keys.Add({"acme", "k1", "acme-key-one"});
  SourceManager mgr;
  DiagEngine diag(mgr);
  EnvelopeEncryptor encryptor("", keys, &diag);
  const std::string kNames =
      "`pragma protect data_keyowner=\"acme\", data_keyname=\"k1\"\n";
  const std::string kRegion =
      "`pragma protect begin\n  initial secret = 1;\n`pragma protect end\n";
  std::string first = encryptor.Encrypt(kNames, mgr.AddFile("a.sv", kNames));
  std::string second = encryptor.Encrypt(kRegion, mgr.AddFile("b.sv", kRegion));
  EXPECT_EQ(first, kNames);
  EXPECT_NE(second.find("`pragma protect data_block\n"), std::string::npos)
      << second;
  EXPECT_EQ(second.find("initial secret = 1;"), std::string::npos) << second;
  EXPECT_EQ(encryptor.Finish(), "");
  EXPECT_FALSE(diag.HasErrors());
}

TEST(EnvelopeEncryption, ARegionOpenedInOneTextClosesInTheNext) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  EnvelopeEncryptor encryptor("exchange", ProtectKeyList(), &diag);
  const std::string kOpens = "`pragma protect begin\n  initial secret = 1;\n";
  const std::string kCloses =
      "`pragma protect end\nmodule after_m; endmodule\n";
  std::string first = encryptor.Encrypt(kOpens, mgr.AddFile("a.sv", kOpens));
  std::string second = encryptor.Encrypt(kCloses, mgr.AddFile("b.sv", kCloses));
  EXPECT_EQ(first, "");
  EXPECT_NE(second.find("`pragma protect begin_protected"), std::string::npos)
      << second;
  EXPECT_EQ(second.find("initial secret = 1;"), std::string::npos) << second;
  EXPECT_NE(second.find("module after_m; endmodule\n"), std::string::npos);
  EXPECT_EQ(encryptor.Finish(), "");
}

TEST(EnvelopeEncryption, ARegionLeftOpenGoesBackWhenTheRunFinishes) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  EnvelopeEncryptor encryptor("exchange", ProtectKeyList(), &diag);
  const std::string kOpens = "`pragma protect begin\n  initial secret = 1;\n";
  EXPECT_EQ(encryptor.Encrypt(kOpens, mgr.AddFile("a.sv", kOpens)), "");
  EXPECT_EQ(encryptor.Finish(), kOpens);
}

}  // namespace
