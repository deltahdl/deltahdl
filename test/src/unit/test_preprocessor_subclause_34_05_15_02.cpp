#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_block_lines.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";
constexpr std::string_view kRegionKey = "one-key-of-the-authors-own";

constexpr std::string_view kNamedScheme = "base64";

constexpr std::string_view kAnnouncingDirective =
    "`pragma protect data_block\n";

constexpr std::string_view kDigestAnnouncingDirective =
    "`pragma protect digest_block\n";

std::string RegionEncodedIn(std::string_view scheme, std::string_view asks) {
  std::string text = "`pragma protect begin\n";
  text += "`pragma protect encoding=(enctype=\"";
  text.append(scheme).append("\")\n");
  text.append(asks);
  text.append(kSealedDesign);
  text += "`pragma protect end\n";
  return text;
}

std::string EnvelopeOfRegion(std::string_view scheme, std::string_view asks) {
  std::string envelope =
      EncryptEnvelopes(RegionEncodedIn(scheme, asks), std::string(kRegionKey));
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  return envelope;
}

std::string EnvelopeEncodedIn(std::string_view scheme) {
  return EnvelopeOfRegion(scheme, "");
}

std::string BlockBeneathTheKeyword(std::string_view envelope) {
  size_t announced = envelope.find(kAnnouncingDirective);
  if (announced == std::string_view::npos) return {};
  std::string_view beneath =
      envelope.substr(announced + kAnnouncingDirective.size());
  return std::string(beneath.substr(0, beneath.find('\n')));
}

std::string BlockLinesBeneathTheKeyword(std::string_view envelope) {
  size_t announced = envelope.find(kAnnouncingDirective);
  if (announced == std::string_view::npos) return {};
  std::string_view beneath =
      envelope.substr(announced + kAnnouncingDirective.size());
  return std::string(beneath.substr(0, beneath.find("\n`pragma")));
}

PreprocConfig KeyOnly() {
  PreprocConfig config;
  config.protect_key = std::string(kRegionKey);
  return config;
}

std::string ReadBack(const std::string& src, PreprocFixture& f) {
  return Preprocess(src, f, KeyOnly());
}

TEST(ProtectDataBlockDescription, TheEnvelopeDeclaresTheSchemeTheRegionNamed) {
  std::string envelope = EnvelopeEncodedIn(kNamedScheme);
  EXPECT_NE(envelope.find("enctype=\"base64\""), std::string::npos) << envelope;
  EXPECT_NE(envelope.find(kAnnouncingDirective), std::string::npos) << envelope;
}

TEST(ProtectDataBlockDescription, TheBlockStandsOnTheLineBeneathTheKeyword) {
  std::string envelope = EnvelopeEncodedIn(kNamedScheme);
  ASSERT_EQ(envelope.find("`pragma protect data_block=\""), std::string::npos)
      << envelope;
  std::string cleartext;
  ASSERT_TRUE(DecryptProtectedRegion(BlockLinesBeneathTheKeyword(envelope),
                                     kRegionKey, &cleartext, kNamedScheme))
      << envelope;
  EXPECT_NE(cleartext.find(kSealedDesign), std::string::npos) << cleartext;
}

TEST(ProtectDataBlockDescription, ReversingTheDeclaredSchemeOpensTheBlock) {
  PreprocFixture f;
  std::string read = ReadBack(EnvelopeEncodedIn(kNamedScheme), f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(read.find(kSealedDesign), std::string::npos) << read;
}

TEST(ProtectDataBlockDescription, ABlockStandingOnSeveralLinesIsReadWhole) {
  std::string envelope = EnvelopeEncodedIn(kNamedScheme);
  std::string broken =
      WithBlockBrokenIntoLines(envelope, kAnnouncingDirective, 3);
  ASSERT_NE(broken, envelope);
  ASSERT_LT(BlockBeneathTheKeyword(broken).size(),
            BlockBeneathTheKeyword(envelope).size());

  PreprocFixture f;
  std::string read = ReadBack(broken, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(read.find(kSealedDesign), std::string::npos) << read;
}

struct ReadKeepingTheComparison {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, KeyOnly()};
  std::string text;

  explicit ReadKeepingTheComparison(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }
};

TEST(ProtectDataBlockDescription, TheDirectiveEndingABlockStillTakesEffect) {
  std::string broken = WithBlockBrokenIntoLines(
      EnvelopeOfRegion(kNamedScheme, kDigestAnnouncingDirective),
      kAnnouncingDirective, 3);
  ASSERT_NE(broken.find(kDigestAnnouncingDirective), std::string::npos)
      << broken;

  ReadKeepingTheComparison run(broken);
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_NE(run.text.find(kSealedDesign), std::string::npos) << run.text;
  EXPECT_EQ(run.pp.LastDigestBlockCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectDataBlockDescription, TheEncodedCharactersAreWhatIsReversed) {
  std::string envelope = EnvelopeEncodedIn(kNamedScheme);
  auto at = envelope.find(kAnnouncingDirective);
  ASSERT_NE(at, std::string::npos) << envelope;
  auto target = at + kAnnouncingDirective.size() + 8;
  ASSERT_LT(target, envelope.size());
  ASSERT_NE(envelope[target], '\n') << envelope;
  std::string altered = envelope;
  altered[target] = (altered[target] == 'A') ? 'B' : 'A';

  PreprocFixture f;
  std::string read = ReadBack(altered, f);
  EXPECT_EQ(read.find(kSealedDesign), std::string::npos) << read;
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 8,
      "34.3.2"));
}

}  // namespace
