#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kAuthorKey = "acme-exchange-key";
constexpr std::string_view kOtherKey = "not-the-authors-key";

constexpr std::string_view kSealedBlockAnnouncement =
    "`pragma protect data_block\n";

struct ProducedText {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  ProducedText(const std::string& src, std::string_view key) {
    PreprocConfig config;
    config.protect_key = key;
    Preprocessor pp(mgr, diag, config);
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string_view::npos;
  }

  size_t At(std::string_view needle) const { return text.find(needle); }
};

std::string EnvelopeOf(const std::string& body,
                       std::string_view key = kAuthorKey) {
  std::string region = "`pragma protect begin\n";
  region += body;
  region += "`pragma protect end\n";
  return EncryptEnvelopes(region, key);
}

TEST(EnvelopeDecryption, TheRecoveredTextStandsWhereTheEnvelopeWas) {
  std::string src = "initial before_value = 1;\n";
  src += EnvelopeOf("initial sealed_value = 2;\n");
  src += "initial after_value = 3;\n";
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("initial sealed_value = 2;"));
  EXPECT_LT(run.At("initial before_value = 1;"),
            run.At("initial sealed_value = 2;"));
  EXPECT_LT(run.At("initial sealed_value = 2;"),
            run.At("initial after_value = 3;"));
}

TEST(EnvelopeDecryption, TheEnvelopeIsGoneFromTheProducedText) {
  ProducedText run(EnvelopeOf("initial sealed_value = 2;\n"), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.Holds("begin_protected"));
  EXPECT_FALSE(run.Holds("data_block"));
  EXPECT_FALSE(run.Holds("end_protected"));
}

TEST(EnvelopeDecryption, EachEnvelopeIsReplacedByItsOwnRecordedText) {
  std::string src = EnvelopeOf("initial first_value = 1;\n");
  src += "initial between_value = 2;\n";
  src += EnvelopeOf("initial third_value = 3;\n");
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_LT(run.At("initial first_value = 1;"),
            run.At("initial between_value = 2;"));
  EXPECT_LT(run.At("initial between_value = 2;"),
            run.At("initial third_value = 3;"));
  EXPECT_NE(run.At("initial third_value = 3;"), std::string::npos);
}

TEST(EnvelopeDecryption, AnEnvelopeCarryingItsDescriptionIsStillReplaced) {
  std::string authored = "`pragma protect author=\"Acme Corp\"\n";
  authored += "`pragma protect data_method=\"x-caesar\", ";
  authored += "data_keyname=\"rot13\", begin\n";
  authored += "initial sealed_value = 2;\n";
  authored += "`pragma protect end\n";
  ProducedText run(EncryptEnvelopes(authored, kAuthorKey), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("initial sealed_value = 2;"));
  EXPECT_FALSE(run.Holds("Acme Corp"));
  EXPECT_FALSE(run.Holds("rot13"));
}

TEST(EnvelopeDecryption, AnEnvelopeRecordingEmptyTextIsReplacedByNothing) {
  std::string src = "initial before_value = 1;\n";
  src += EnvelopeOf("");
  src += "initial after_value = 3;\n";
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("initial before_value = 1;"));
  EXPECT_TRUE(run.Holds("initial after_value = 3;"));
  EXPECT_FALSE(run.Holds("data_block"));
}

TEST(EnvelopeDecryption, TextHoldingNoEnvelopeIsLeftAsItStands) {
  std::string src = "initial before_value = 1;\n";
  src += "initial after_value = 3;\n";
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("initial before_value = 1;"));
  EXPECT_TRUE(run.Holds("initial after_value = 3;"));
}

TEST(EnvelopeDecryption, AMacroUsedInTheRecoveredTextIsSubstituted) {
  std::string src = "`define WIDTH 8\n";
  src += EnvelopeOf("logic [`WIDTH-1:0] sealed_bus;\n");
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("logic [8-1:0] sealed_bus;"));
  EXPECT_FALSE(run.Holds("`WIDTH"));
}

TEST(EnvelopeDecryption, AMacroDefinedInTheRecoveredTextIsInEffectAfterIt) {
  std::string src = EnvelopeOf("`define WIDTH 8\n");
  src += "logic [`WIDTH-1:0] open_bus;\n";
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("logic [8-1:0] open_bus;"));
  EXPECT_FALSE(run.Holds("`WIDTH"));
}

TEST(EnvelopeDecryption, AMacroDefinedAndUsedInTheRecoveredTextIsSubstituted) {
  std::string body = "`define WIDTH 8\n";
  body += "logic [`WIDTH-1:0] sealed_bus;\n";
  ProducedText run(EnvelopeOf(body), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("logic [8-1:0] sealed_bus;"));
  EXPECT_FALSE(run.Holds("`WIDTH"));
}

TEST(EnvelopeDecryption, AMacroWithArgumentsInTheRecoveredTextIsSubstituted) {
  std::string src = "`define MSB(w) ((w)-1)\n";
  src += EnvelopeOf("logic [`MSB(8):0] sealed_bus;\n");
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("logic [((8)-1):0] sealed_bus;"));
  EXPECT_FALSE(run.Holds("`MSB"));
}

TEST(EnvelopeDecryption, AnUndefinedMacroInTheRecoveredTextIsReported) {
  ProducedText run(EnvelopeOf("logic [`WIDTH-1:0] sealed_bus;\n"), kAuthorKey);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(), "undefined macro 'WIDTH'",
                            1, "22.5.1"));
}

TEST(EnvelopeDecryption, AnEnvelopeInTheRecoveredTextIsDecryptedToo) {
  std::string sealed = EnvelopeOf("initial sealed_value = 2;\n");
  ProducedText run(EnvelopeOf(sealed), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("initial sealed_value = 2;"));
  EXPECT_FALSE(run.Holds("data_block"));
}

TEST(EnvelopeDecryption, EveryLevelOfEnclosedEnvelopeIsDecrypted) {
  std::string innermost = EnvelopeOf("initial third_value = 3;\n");
  std::string middle = "initial second_value = 2;\n";
  middle += innermost;
  std::string outer = "initial first_value = 1;\n";
  outer += EnvelopeOf(middle);
  ProducedText run(EnvelopeOf(outer), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_LT(run.At("initial first_value = 1;"),
            run.At("initial second_value = 2;"));
  EXPECT_LT(run.At("initial second_value = 2;"),
            run.At("initial third_value = 3;"));
  EXPECT_NE(run.At("initial third_value = 3;"), std::string::npos);
}

TEST(EnvelopeDecryption, EveryEnclosedEnvelopeOfOneRecoveredTextIsDecrypted) {
  std::string body = EnvelopeOf("initial first_value = 1;\n");
  body += EnvelopeOf("initial second_value = 2;\n");
  ProducedText run(EnvelopeOf(body), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("initial first_value = 1;"));
  EXPECT_LT(run.At("initial first_value = 1;"),
            run.At("initial second_value = 2;"));
}

TEST(EnvelopeDecryption, AnEnclosedEnvelopeUnderAnotherKeyIsReported) {
  std::string body = "initial outer_value = 1;\n";
  body += EnvelopeOf("initial inner_value = 2;\n", kOtherKey);
  ProducedText run(EnvelopeOf(body), kAuthorKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(body, kSealedBlockAnnouncement) + 1, "34.3.2"));
  EXPECT_TRUE(run.Holds("initial outer_value = 1;"));
  EXPECT_FALSE(run.Holds("initial inner_value = 2;"));
}

TEST(EnvelopeDecryption, AMacroInAnEnclosedEnvelopeIsSubstitutedAfterBoth) {
  std::string body = "`define WIDTH 8\n";
  body += EnvelopeOf("logic [`WIDTH-1:0] sealed_bus;\n");
  ProducedText run(EnvelopeOf(body), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("logic [8-1:0] sealed_bus;"));
  EXPECT_FALSE(run.Holds("`WIDTH"));
}

TEST(EnvelopeDecryption, AnEnclosedEnvelopesResetLeavesTheOuterDigestAlone) {
  std::string inner = EnvelopeOf("initial sealed_value = 2;\n");
  ASSERT_NE(inner.find("`pragma protect reset"), std::string::npos) << inner;
  ProtectEncoding encoding = DefaultProtectEncoding();
  std::string outer = "`pragma protect begin_protected\n";
  outer += "`pragma protect digest_method=\"md5\"\n";
  outer +=
      ProtectEncodedValueDirective(encoding, ProtectedRegionBlockSize(inner));
  outer += kSealedBlockAnnouncement;
  outer += EncryptProtectedRegion(inner, kAuthorKey) + "\n";
  ProtectDigestBlockPolicy policy;
  policy.requested = true;
  policy.method = "md5";
  policy.key = std::string(kAuthorKey);
  outer += ProtectDigestBlockDirectives(inner, policy, encoding);
  outer += "`pragma protect end_protected\n";
  ProducedText run(outer, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_TRUE(run.Holds("initial sealed_value = 2;")) << run.text;
}

}  // namespace
