#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "fixture_protect_read.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

struct ProtectKeyBlockSyntaxTest : ::testing::Test {
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

TEST_F(ProtectKeyBlockSyntaxTest,
       KeyBlockDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess("module m;\n`pragma protect key_block\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST_F(ProtectKeyBlockSyntaxTest,
       KeyBlockConsumesOnlyDirectiveLineFollowingLineKept) {
  auto result = Preprocess("`pragma protect key_block\nENCODEDKEYBLOCKDATA\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("ENCODEDKEYBLOCKDATA"), std::string::npos);
}

TEST_F(ProtectKeyBlockSyntaxTest, KeyBlockHasNoSameLineArgument) {
  auto result = Preprocess(
      "module m;\n`pragma protect key_block TRAILINGTOKEN\nendmodule\n");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 2,
                            "22.11"));
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("TRAILINGTOKEN"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kKeyName = "wrapping-2027";
constexpr std::string_view kEntityKey = "meridian-trust-wrapping-key";

constexpr std::string_view kDataKeyName = "design-2027";

constexpr std::string_view kEncodingSealedDesign =
    "module sealed_m; endmodule\n";

constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";

ProtectKeyList TheEntitysKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, kEntityKey));
  return keys;
}

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string EnvelopeWithAKeyBlock() {
  std::string region = "`pragma protect begin\n";
  region.append(Writes("key_keyowner", kEntity));
  region.append(Writes("key_keyname", kKeyName));
  region.append(Writes("data_keyname", kDataKeyName));
  region.append(kEncodingSealedDesign);
  region.append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(region, {}, TheEntitysKey());
  EXPECT_FALSE(Holds(envelope, kEncodingSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, kKeyBlockLine)) << envelope;
  return envelope;
}

std::string EnvelopeAnnouncing(std::string_view announced) {
  std::string envelope = EnvelopeWithAKeyBlock();
  size_t at = envelope.find(kKeyBlockLine);
  EXPECT_NE(at, std::string::npos) << envelope;
  std::string rewritten = envelope;
  rewritten.replace(at, kKeyBlockLine.size(), announced);
  return rewritten;
}

std::string BlockLineOf(const std::string& envelope) {
  size_t at = envelope.find(kKeyBlockLine);
  EXPECT_NE(at, std::string::npos) << envelope;
  size_t from = at + kKeyBlockLine.size();
  return envelope.substr(from, envelope.find('\n', from) - from);
}

TEST(ProtectKeyBlockSyntax, TheKeywordSpeaksForTheLineBeneathIt) {
  ReadSource run(EnvelopeWithAKeyBlock(),
                 ReadSource::KeysConfig(TheEntitysKey()));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_TRUE(Holds(run.text, kEncodingSealedDesign)) << run.text;
}

TEST(ProtectKeyBlockSyntax, TheLineTheKeywordSpokeForIsNotDesignText) {
  std::string envelope = EnvelopeWithAKeyBlock();
  ReadSource run(envelope, ReadSource::KeysConfig(TheEntitysKey()));
  EXPECT_FALSE(Holds(run.text, BlockLineOf(envelope))) << run.text;
}

TEST(ProtectKeyBlockSyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  std::string envelope =
      EnvelopeAnnouncing("`pragma protect key_block=\"a-value-of-its-own\"\n");
  ReadSource run(envelope, ReadSource::KeysConfig(TheEntitysKey()));
  EXPECT_FALSE(Holds(run.text, kEncodingSealedDesign)) << run.text;
  EXPECT_TRUE(Holds(run.text, BlockLineOf(EnvelopeWithAKeyBlock())))
      << run.text;
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 15,
      "34.3.2"));
}

TEST(ProtectKeyBlockSyntax, AListAgainstTheKeywordSpeaksForNoLine) {
  ReadSource run(
      EnvelopeAnnouncing("`pragma protect key_block=(bytes=\"20\")\n"),
      ReadSource::KeysConfig(TheEntitysKey()));
  EXPECT_FALSE(Holds(run.text, kEncodingSealedDesign)) << run.text;
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 15,
      "34.3.2"));
}

TEST(ProtectKeyBlockSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  ReadSource run(EnvelopeAnnouncing("`pragma protect key_block_of_theirs\n"),
                 ReadSource::KeysConfig(TheEntitysKey()));
  EXPECT_FALSE(Holds(run.text, kEncodingSealedDesign)) << run.text;
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 15,
      "34.3.2"));
}

TEST(ProtectKeyBlockSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect key_block =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectKeyBlockSyntax, TheSpellingDecidesWhatIsAnnouncedNotWhatIsFound) {
  std::string src = "module m;\n";
  src.append(kKeyBlockLine).append("endmodule\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "key_block is written where no previously", 2,
                            "34.5.27"));
}

}  // namespace
