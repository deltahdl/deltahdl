#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kAuthorKey = "acme-exchange-key";

constexpr std::string_view kSealedDesign = "  initial result = 42;\n";

constexpr std::string_view kSealedStatement = "initial result = 42;";

constexpr std::string_view kKeyProvider = "aegis-custody";
constexpr std::string_view kKeyProviderKeyName = "wrapping-2026";
constexpr std::string_view kKeyProviderKey = "aegis-custody-wrapping-key";

constexpr std::string_view kSecondProvider = "borealis-trust";
constexpr std::string_view kSecondProviderKeyName = "wrapping-2027";
constexpr std::string_view kSecondProviderKey = "borealis-trust-wrapping-key";

constexpr std::string_view kDataKeyOwner = "meridian-ip";
constexpr std::string_view kDataKeyName = "sealing-2026";

constexpr std::string_view kDigestAlgorithm = "md5";

constexpr std::string_view kDesignAuthor = "Acme Corp";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string Region(std::string_view described, std::string_view body) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(body);
  text.append("`pragma protect end\n");
  return text;
}

std::string DataBlockOf(const std::string& written) {
  constexpr std::string_view kAnnouncement = "`pragma protect data_block\n";
  size_t at = written.find(kAnnouncement);
  if (at == std::string::npos) return {};
  size_t start = at + kAnnouncement.size();
  size_t end = written.find('\n', start);
  if (end == std::string::npos) return {};
  return written.substr(start, end - start);
}

std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, kAuthorKey);
}

std::string TwoSealedModels(std::string_view ahead,
                            std::string_view described) {
  std::string src(ahead);
  src += Region(described, "  int first = 1;\n");
  src += Region(described, "  int second = 2;\n");
  return src;
}

constexpr std::string_view kEnvelopeOpening = "`pragma protect begin_protected";

struct WrittenEnvelopes {
  std::string first;
  std::string second;
};

WrittenEnvelopes EnvelopesOf(const std::string& written) {
  size_t first = written.find(kEnvelopeOpening);
  EXPECT_NE(first, std::string::npos);
  if (first == std::string::npos) return {};
  size_t second =
      written.find(kEnvelopeOpening, first + kEnvelopeOpening.size());
  EXPECT_NE(second, std::string::npos);
  if (second == std::string::npos) return {};
  return {written.substr(first, second - first), written.substr(second)};
}

struct EncryptionRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit EncryptionRun(const std::string& src)
      : text(EncryptEnvelopes(src, kAuthorKey, ProtectKeyList(), &diag,
                              mgr.AddFile("<test>", src))) {}
};

struct ReadSource {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  ReadSource(const std::string& src, std::string_view key)
      : pp(mgr, diag, KeyConfig(key)) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  static PreprocConfig KeyConfig(std::string_view key) {
    PreprocConfig config;
    config.protect_key = std::string(key);
    return config;
  }
};

TEST(ProtectBeginEncryptionInput, TheExpressionIsWhereEncryptionStarts) {
  std::string src = "module secret;\n  int cleartext = 1;\n";
  src += Region("", kSealedDesign);
  EncryptionRun run(src);
  EXPECT_TRUE(Holds(run.text, "int cleartext = 1;"));
  EXPECT_FALSE(Holds(run.text, kSealedStatement));
}

TEST(ProtectBeginEncryptionInput, AListedExpressionMarksThePointToo) {
  EncryptionRun run(
      "  int cleartext = 1;\n"
      "`pragma protect author=\"Acme Corp\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(run.text, "int cleartext = 1;"));
  EXPECT_FALSE(Holds(run.text, kSealedStatement));
}

TEST(ProtectBeginEncryptionInput, WithNoOpeningExpressionNothingIsSealed) {
  std::string src = "  initial result = 42;\n`pragma protect end\n";
  EXPECT_EQ(Encrypted(src), src);
}

TEST(ProtectBeginEncryptionInput, EachExpressionMarksItsOwnPoint) {
  std::string src = Region("", "  initial first = 1;\n");
  src += "  int between = 3;\n";
  src += Region("", "  initial second = 2;\n");
  EncryptionRun run(src);
  EXPECT_FALSE(Holds(run.text, "initial first = 1;"));
  EXPECT_FALSE(Holds(run.text, "initial second = 2;"));
  EXPECT_TRUE(Holds(run.text, "int between = 3;"));
}

TEST(ProtectBeginEncryptionInput, ARegionOpenedInsideAnOpenRegionIsReported) {
  EncryptionRun run(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect begin\n"
      "  initial other = 7;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "opens a region inside a begin-end block", 3,
                            "34.5.1"));
}

TEST(ProtectBeginEncryptionInput, TheReportedInputIsStillTransformed) {
  EncryptionRun run(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect begin\n"
      "  initial other = 7;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(run.text, "`pragma protect begin_protected\n"));
  EXPECT_FALSE(Holds(run.text, kSealedStatement));
  EXPECT_FALSE(Holds(run.text, "initial other = 7;"));
}

TEST(ProtectBeginEncryptionInput, TheFirstClosingExpressionAnswersTheOpening) {
  EncryptionRun run(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect begin\n"
      "`pragma protect end\n"
      "  int after = 3;\n");
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "opens a region inside a begin-end block", 3,
                            "34.5.1"));
  EXPECT_FALSE(Holds(run.text, kSealedStatement));
  EXPECT_TRUE(Holds(run.text, "int after = 3;"));
}

TEST(ProtectBeginEncryptionInput, RegionsWrittenOneAfterAnotherAreNoNesting) {
  std::string src = Region("", "  initial first = 1;\n");
  src += Region("", "  initial second = 2;\n");
  EncryptionRun run(src);
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
  EXPECT_EQ(TimesWritten(run.text, "`pragma protect begin_protected"), 2U);
}

TEST(ProtectBeginEncryptionInput, AValuedWordInsideTheRegionIsNoNesting) {
  EncryptionRun run(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect begin=\"again\"\n"
      "`pragma protect end\n");
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectBeginEncryptionInput, ANestedExpressionInAListIsReportedToo) {
  EncryptionRun run(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect author=\"Acme Corp\", begin\n"
      "`pragma protect end\n");
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "opens a region inside a begin-end block", 3,
                            "34.5.1"));
}

TEST(ProtectBeginEncryptionInput, ANestedRegionIsReportedWithNoKeyToo) {
  std::string src =
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect begin\n"
      "`pragma protect end\n";
  SourceManager mgr;
  DiagEngine diag(mgr);
  EXPECT_EQ(EncryptEnvelopes(src, "", ProtectKeyList(), &diag,
                             mgr.AddFile("<test>", src)),
            src);
  EXPECT_TRUE(ReportedError(diag.Diagnostics(),
                            "opens a region inside a begin-end block", 3,
                            "34.5.1"));
}

TEST(ProtectBeginEncryptionInput, APreviouslyProtectedBlockInsideIsSealed) {
  std::string inner = Encrypted(Region("", "  initial inner = 2;\n"));
  EncryptionRun run(Region("", inner));
  EXPECT_TRUE(Holds(inner, "`pragma protect begin_protected"));
  EXPECT_FALSE(Holds(run.text, inner));
  EXPECT_EQ(TimesWritten(run.text, "`pragma protect begin_protected"), 1U);
}

TEST(ProtectBeginEncryptionInput, AWordInsideThatBlockIsNoNesting) {
  EncryptionRun run(
      "`pragma protect begin\n"
      "`pragma protect begin_protected\n"
      "`pragma protect begin\n"
      "`pragma protect end_protected\n"
      "`pragma protect end\n");
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectBeginEncryptionInput, TheBlockClosingMatchesItsOwnOpening) {
  std::string sealed = Encrypted(Region("", "  initial inner = 2;\n"));
  std::string enclosing = "`pragma protect begin_protected\n";
  enclosing += sealed;
  enclosing += "`pragma protect begin\n";
  enclosing += "`pragma protect end_protected\n";
  EncryptionRun run(Region("", enclosing));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
  EXPECT_FALSE(Holds(run.text, sealed));
}

TEST(ProtectBeginEncryptionInput, ThatBlocksDescriptionDescribesNothing) {
  std::string inner = "`pragma protect begin_protected\n";
  inner += Writes("data_method", "acme-cipher");
  inner += "`pragma protect data_block\nNOTABLOCKOFTHISTOOLS\n";
  inner += "`pragma protect end_protected\n";
  EncryptionRun run(Region("", inner));
  EXPECT_FALSE(Holds(run.text, "acme-cipher"));
  EXPECT_FALSE(Holds(run.text, "NOTABLOCKOFTHISTOOLS"));
}

TEST(ProtectBeginEncryptionInput, TwoSuchBlocksInsideOneRegionBothSurvive) {
  std::string first = Encrypted(Region("", "  initial first = 1;\n"));
  std::string second = Encrypted(Region("", "  initial second = 2;\n"));
  EncryptionRun run(Region("", first + second));
  ReadSource read(run.text, kAuthorKey);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(Holds(read.text, "initial first = 1;"));
  EXPECT_TRUE(Holds(read.text, "initial second = 2;"));
}

TEST(ProtectBeginEncryptionInput, TheSameBlockOutsideEveryRegionIsLeftAlone) {
  std::string inner = Encrypted(Region("", "  initial inner = 2;\n"));
  EncryptionRun run(inner);
  EXPECT_EQ(run.text, inner);
}

TEST(ProtectBeginEncryptionOutput, TheOpeningExpressionIsReplaced) {
  EncryptionRun run(Region("", kSealedDesign));
  EXPECT_TRUE(Holds(run.text, "`pragma protect begin_protected\n"));
  EXPECT_FALSE(Holds(run.text, "`pragma protect begin\n"));
}

TEST(ProtectBeginEncryptionOutput, OnlyTheDelimitingWordChangesOnItsLine) {
  EncryptionRun run(
      "`pragma protect author=\"Acme Corp\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  constexpr std::string_view kTransformed =
      "`pragma protect author=\"Acme Corp\", begin_protected\n";
  EXPECT_TRUE(Holds(run.text, kTransformed));
}

TEST(ProtectBeginEncryptionOutput, ExpressionsAfterTheWordAreTheRegions) {
  EncryptionRun run(
      "`pragma protect begin, comment=\"the region below\"\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(run.text, "`pragma protect begin_protected\n")) << run.text;
  EXPECT_TRUE(Holds(run.text, "`pragma protect comment=\"the region below\"\n"))
      << run.text;
}

TEST(ProtectBeginEncryptionOutput, ALicenceOnADelimitingLineIsEncrypted) {
  constexpr std::string_view kRuntime =
      "runtime_license=(library=\"lic.so\",entry=\"chk\",feature=\"run\")";
  constexpr std::string_view kDecrypt =
      "decrypt_license=(library=\"lic.so\",entry=\"chk\",feature=\"open\")";
  std::string src = "`pragma protect begin, ";
  src.append(kRuntime).append("\n  initial result = 42;\n");
  src.append("`pragma protect ").append(kDecrypt).append(", end\n");
  EncryptionRun run(src);
  EXPECT_FALSE(Holds(run.text, "_license")) << run.text;
  constexpr std::string_view kBlockLine = "`pragma protect data_block\n";
  size_t at = run.text.find(kBlockLine);
  ASSERT_NE(at, std::string::npos) << run.text;
  size_t from = at + kBlockLine.size();
  std::string block = run.text.substr(from, run.text.find('\n', from) - from);
  std::string recovered;
  ASSERT_TRUE(DecryptProtectedRegion(block, kAuthorKey, &recovered));
  EXPECT_TRUE(Holds(recovered, kRuntime)) << recovered;
  EXPECT_TRUE(Holds(recovered, kDecrypt)) << recovered;
}

TEST(ProtectBeginEncryptionOutput, ACommentAfterTheDelimiterIsNotCarried) {
  EncryptionRun run(
      "`pragma protect begin // the region starts here\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(run.text, "`pragma protect begin_protected\n"));
  EXPECT_FALSE(Holds(run.text, "the region starts here"));
}

TEST(ProtectBeginEncryptionOutput, WithNoKeyTheExpressionStandsAsWritten) {
  std::string src = Region("", kSealedDesign);
  EXPECT_EQ(EncryptEnvelopes(src, ""), src);
}

TEST(ProtectBeginEncryptionOutput, TheRequiredExpressionsPrecedeTheClosing) {
  EncryptionRun run(Region("", kSealedDesign));
  size_t opening = run.text.find("`pragma protect begin_protected");
  size_t closing = run.text.find("`pragma protect end_protected");
  size_t agent = run.text.find("`pragma protect encrypt_agent=");
  size_t method = run.text.find("`pragma protect data_method=");
  size_t encoding = run.text.find("`pragma protect encoding=");
  ASSERT_NE(opening, std::string::npos);
  ASSERT_NE(closing, std::string::npos);
  EXPECT_LT(opening, agent);
  EXPECT_LT(agent, closing);
  EXPECT_LT(opening, method);
  EXPECT_LT(method, closing);
  EXPECT_LT(opening, encoding);
  EXPECT_LT(encoding, closing);
}

TEST(ProtectBeginEncryptionOutput, NothingRequiredAsOutputFollowsTheClose) {
  EncryptionRun run(Region("", kSealedDesign));
  size_t closing = run.text.find("`pragma protect end_protected");
  ASSERT_NE(closing, std::string::npos);
  std::string after = run.text.substr(closing);
  EXPECT_FALSE(Holds(after, "`pragma protect encrypt_agent="));
  EXPECT_FALSE(Holds(after, "`pragma protect data_method="));
  EXPECT_FALSE(Holds(after, "`pragma protect encoding="));
  EXPECT_FALSE(Holds(after, "`pragma protect data_block"));
  EXPECT_FALSE(Holds(after, "`pragma protect key_block"));
}

TEST(ProtectBeginEncryptionOutput, TheTwoBlocksStandInsideTheWrittenEnvelope) {
  ProtectKeyList keys;
  keys.Add(KeyOf(kKeyProvider, kKeyProviderKeyName, kKeyProviderKey));
  std::string described = Writes("key_keyowner", kKeyProvider);
  described += Writes("key_keyname", kKeyProviderKeyName);
  std::string written =
      EncryptEnvelopes(Region(described, kSealedDesign), "", keys);
  size_t opening = written.find("`pragma protect begin_protected");
  size_t closing = written.find("`pragma protect end_protected");
  size_t key_block = written.find("`pragma protect key_block");
  size_t data_block = written.find("`pragma protect data_block");
  ASSERT_NE(opening, std::string::npos);
  ASSERT_NE(closing, std::string::npos);
  ASSERT_NE(key_block, std::string::npos);
  ASSERT_NE(data_block, std::string::npos);
  EXPECT_LT(opening, key_block);
  EXPECT_LT(key_block, closing);
  EXPECT_LT(opening, data_block);
  EXPECT_LT(data_block, closing);
}

TEST(ProtectBeginEncryptionOutput, EveryKeyBlockAskedForIsInsideTheEnvelope) {
  ProtectKeyList keys;
  keys.Add(KeyOf(kKeyProvider, kKeyProviderKeyName, kKeyProviderKey));
  keys.Add(KeyOf(kSecondProvider, kSecondProviderKeyName, kSecondProviderKey));
  std::string described = Writes("key_keyowner", kKeyProvider);
  described += Writes("key_keyname", kKeyProviderKeyName);
  described += Writes("key_keyowner", kSecondProvider);
  described += Writes("key_keyname", kSecondProviderKeyName);
  std::string written =
      EncryptEnvelopes(Region(described, kSealedDesign), "", keys);
  size_t opening = written.find("`pragma protect begin_protected");
  size_t closing = written.find("`pragma protect end_protected");
  size_t last_block = written.rfind("`pragma protect key_block");
  ASSERT_NE(opening, std::string::npos);
  ASSERT_NE(closing, std::string::npos);
  ASSERT_NE(last_block, std::string::npos);
  EXPECT_EQ(TimesWritten(written, "`pragma protect key_block"), 2U);
  EXPECT_LT(opening, last_block);
  EXPECT_LT(last_block, closing);
}

TEST(ProtectBeginEncryptionOutput, TwoWrittenEnvelopesInOneStreamBothOpen) {
  std::string first = Encrypted(Region("", "  int a = 1;\n"));
  std::string second = Encrypted(Region("", "  int b = 2;\n"));
  EXPECT_EQ(TimesWritten(first, "`pragma protect data_block\n"), 1U);
  EXPECT_EQ(TimesWritten(second, "`pragma protect data_block\n"), 1U);
  ReadSource run(first + second, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "int a = 1;"));
  EXPECT_TRUE(Holds(run.text, "int b = 2;"));
}

TEST(ProtectBeginEncryptionOutput, EachEnvelopeStatesTheDigestMethodInEffect) {
  std::string stated = Writes("digest_method", kDigestAlgorithm);
  WrittenEnvelopes written =
      EnvelopesOf(Encrypted(TwoSealedModels(stated, "")));
  EXPECT_TRUE(Holds(written.first, stated));
  EXPECT_TRUE(Holds(written.second, stated));
}

TEST(ProtectBeginEncryptionOutput, EachEnvelopeCarriesTheKeyNamesInEffect) {
  std::string owner = Writes("data_keyowner", kDataKeyOwner);
  std::string named = Writes("data_keyname", kDataKeyName);
  WrittenEnvelopes written =
      EnvelopesOf(Encrypted(TwoSealedModels(owner + named, "")));
  EXPECT_TRUE(Holds(written.first, owner));
  EXPECT_TRUE(Holds(written.first, named));
  EXPECT_TRUE(Holds(written.second, owner));
  EXPECT_TRUE(Holds(written.second, named));
}

TEST(ProtectBeginEncryptionOutput, ADigestMethodIsStatedOnlyWhereOneIsAsked) {
  std::string stated = Writes("digest_method", kDigestAlgorithm);
  WrittenEnvelopes inside = EnvelopesOf(Encrypted(TwoSealedModels("", stated)));
  WrittenEnvelopes neither = EnvelopesOf(Encrypted(TwoSealedModels("", "")));
  EXPECT_TRUE(Holds(inside.first, stated));
  EXPECT_TRUE(Holds(inside.second, stated));
  EXPECT_FALSE(Holds(neither.first, "`pragma protect digest_method"));
  EXPECT_FALSE(Holds(neither.second, "`pragma protect digest_method"));
}

TEST(ProtectBeginEncryptionOutput, NoEnvelopeCarriesAnAuthorWrittenAhead) {
  std::string written =
      Encrypted(TwoSealedModels(Writes("author", kDesignAuthor), ""));
  WrittenEnvelopes envelopes = EnvelopesOf(written);
  EXPECT_EQ(TimesWritten(written, "`pragma protect author="), 1U);
  EXPECT_FALSE(Holds(envelopes.first, "`pragma protect author="));
  EXPECT_FALSE(Holds(envelopes.second, "`pragma protect author="));
}

TEST(ProtectBeginEncryptionOutput, TheEnclosedTextIsRecordedOnTheBlock) {
  EncryptionRun run(Region("", kSealedDesign));
  EXPECT_FALSE(Holds(run.text, kSealedStatement));
  ReadSource read(run.text, kAuthorKey);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(Holds(read.text, kSealedStatement));
}

TEST(ProtectBeginEncryptionOutput, ACommentBetweenTheDelimitersIsRecorded) {
  std::string body = "  // the answer\n";
  body += kSealedDesign;
  std::string with = Encrypted(Region("", body));
  std::string without = Encrypted(Region("", kSealedDesign));
  EXPECT_FALSE(Holds(with, "// the answer"));
  EXPECT_FALSE(DataBlockOf(with).empty());
  EXPECT_NE(DataBlockOf(with), DataBlockOf(without));
}

TEST(ProtectBeginEncryptionOutput, AProtectPragmaBetweenThemIsRecordedToo) {
  std::string described = Writes("encrypt_agent", "some-other-sealing-tool");
  std::string with = Encrypted(Region(described, kSealedDesign));
  std::string without = Encrypted(Region("", kSealedDesign));
  EXPECT_FALSE(Holds(with, "some-other-sealing-tool"));
  EXPECT_FALSE(DataBlockOf(with).empty());
  EXPECT_NE(DataBlockOf(with), DataBlockOf(without));
}

TEST(ProtectBeginEncryptionOutput, ADirectiveBetweenThemIsRecordedToo) {
  std::string src = Region("", "`define ANSWER 42\n");
  src += "  int answer = `ANSWER;\n";
  EncryptionRun run(src);
  EXPECT_FALSE(Holds(run.text, "`define ANSWER 42"));
  ReadSource read(run.text, kAuthorKey);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(Holds(read.text, "`ANSWER"));
  EXPECT_TRUE(Holds(read.text, "42"));
}

TEST(ProtectBeginDecryptionInput, TheExpressionDecryptsNothing) {
  ReadSource run(Region("", kSealedDesign), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kSealedStatement));
}

TEST(ProtectBeginDecryptionInput, AnEnvelopeAfterItYieldsTheSameDesign) {
  std::string written = Encrypted(Region("", kSealedDesign));
  ReadSource plain(written, kAuthorKey);
  ReadSource preceded("`pragma protect begin\n" + written, kAuthorKey);
  EXPECT_FALSE(preceded.diag.HasErrors());
  EXPECT_TRUE(Holds(plain.text, kSealedStatement));
  EXPECT_TRUE(Holds(preceded.text, kSealedStatement));
}

TEST(ProtectBeginDecryptionInput, TheExpressionInsideAnEnvelopeChangesNothing) {
  std::string written = Encrypted(Region("", kSealedDesign));
  size_t first_line = written.find('\n');
  ASSERT_NE(first_line, std::string::npos);
  std::string spliced = written.substr(0, first_line + 1);
  spliced += "`pragma protect begin\n";
  spliced += written.substr(first_line + 1);
  ReadSource run(spliced, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kSealedStatement));
}

}  // namespace
