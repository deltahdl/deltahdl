#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kEntity = "acme_semiconductor";

constexpr std::string_view kOtherEntity = "globex_industries";

constexpr std::string_view kSharedValue = "one-value-in-two-places";
constexpr std::string_view kOtherValue = "a-value-of-its-own";

constexpr std::string_view kKeyName = "wrapping-2027";
constexpr std::string_view kEntityKey = "acme-wrapping-key";

constexpr std::string_view kAuthorsKey = "one-key-of-the-authors-own";

constexpr std::string_view kEntityList =
    "(chartered_in=\"delaware\", registry=\"dun-and-bradstreet\")";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

std::string NamesEntity(std::string_view entity) {
  std::string text = "`pragma protect key_keyowner=";
  text.append(entity).append("\n");
  return text;
}

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string Encoded(std::string_view value) {
  return EncodeProtectBlock(value, DefaultProtectEncoding());
}

std::string DesignatesPublicKey(std::string_view value) {
  std::string text = "`pragma protect key_public_key\n";
  text.append(Encoded(value)).append("\n");
  return text;
}

std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

std::string Region(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

ProtectKeyList TheEntitysKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, kEntityKey));
  return keys;
}

struct Read {
  SourceManager mgr;
  DiagEngine diag{mgr};

  explicit Read(const std::string& src) {
    Preprocessor pp(mgr, diag, PreprocConfig{});
    pp.Preprocess(mgr.AddFile("<test>", src));
  }
};

uint32_t LineCarryingOnly(const std::string& src, std::string_view value) {
  std::string alone = "\n";
  alone.append(value).append("\n");
  return LineHolding(src, alone) + 1;
}

constexpr std::string_view kBothNamesOneValue =
    "writes one value against both of the names that designate a key of the "
    "key_keyowner in effect";

TEST(ProtectKeyKeyownerDescription, OneValueAgainstBothDesignationsIsReported) {
  std::string src = ForeignEnvelope(NamesEntity(kEntity) +
                                    Writes("key_keyname", kSharedValue) +
                                    DesignatesPublicKey(kSharedValue));
  Read run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(), kBothNamesOneValue,
                            LineCarryingOnly(src, Encoded(kSharedValue)),
                            "34.5.23"));
}

TEST(ProtectKeyKeyownerDescription, TwoEmptyDesignationsRepeatNothing) {
  Read run(ForeignEnvelope(NamesEntity(kEntity) + Writes("key_keyname", "") +
                           DesignatesPublicKey("")));
  EXPECT_FALSE(run.diag.HasErrors());
}

TEST(ProtectKeyKeyownerDescription, TwoEntitiesKeepTheirDesignationsApart) {
  Read run(ForeignEnvelope(
      NamesEntity(kEntity) + Writes("key_keyname", kSharedValue) +
      NamesEntity(kOtherEntity) + DesignatesPublicKey(kSharedValue)));
  EXPECT_FALSE(run.diag.HasErrors());
}

TEST(ProtectKeyKeyownerDescription, DistinctValuesUnderOneEntityAreLeftAlone) {
  Read run(ForeignEnvelope(NamesEntity(kEntity) +
                           Writes("key_keyname", kSharedValue) +
                           DesignatesPublicKey(kOtherValue)));
  EXPECT_FALSE(run.diag.HasErrors());
}

TEST(ProtectKeyKeyownerDescription, TheEntityGoesOutInTheSpellingItCameInWith) {
  std::string envelope =
      EncryptEnvelopes(Region(NamesEntity(kEntity)), kAuthorsKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesEntity(kEntity))) << envelope;
}

TEST(ProtectKeyKeyownerDescription, TheEntityIsUnchangedInABlocksOwnDirective) {
  std::string envelope = EncryptEnvelopes(
      Region(NamesEntity(kEntity) + Writes("key_keyname", kKeyName)), {},
      TheEntitysKey());
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, "`pragma protect key_block")) << envelope;
  EXPECT_EQ(TimesWritten(envelope, "key_keyowner=\""), 0U) << envelope;
  EXPECT_EQ(TimesWritten(envelope, NamesEntity(kEntity)), 2U) << envelope;
}

TEST(ProtectKeyKeyownerDescription, AListLeavesNoEntityDirectiveOnTheEnvelope) {
  std::string envelope =
      EncryptEnvelopes(Region(NamesEntity(kEntityList)), kAuthorsKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_EQ(TimesWritten(envelope, "key_keyowner="), 0U) << envelope;
}

TEST(ProtectKeyKeyownerDescription, AStringNamesTheEntityTheEnvelopeCarries) {
  std::string envelope =
      EncryptEnvelopes(Region(Writes("key_keyowner", kEntity)), kAuthorsKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, Writes("key_keyowner", kEntity))) << envelope;
}

TEST(ProtectKeyKeyownerDescription, AListLeavesTheStringNamedBeforeItStanding) {
  std::string envelope = EncryptEnvelopes(
      Region(Writes("key_keyowner", kEntity) + NamesEntity(kEntityList)),
      kAuthorsKey);
  EXPECT_TRUE(Holds(envelope, Writes("key_keyowner", kEntity))) << envelope;
  EXPECT_FALSE(Holds(envelope, kEntityList)) << envelope;
}

TEST(ProtectKeyKeyownerDescription, TheEntityAndTheNameOpenTheKeyBlock) {
  std::string envelope = EncryptEnvelopes(
      Region(NamesEntity(kEntity) + Writes("key_keyname", kKeyName)), {},
      TheEntitysKey());
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = TheEntitysKey();
  Preprocessor pp(mgr, diag, std::move(config));
  std::string text = pp.Preprocess(mgr.AddFile("<test>", envelope));
  EXPECT_FALSE(diag.HasErrors()) << text;
  EXPECT_TRUE(Holds(text, kSealedDesign)) << text;
}

TEST(ProtectKeyKeyownerDescription, AnotherEntityHoldingTheKeyReachesNothing) {
  std::string envelope = EncryptEnvelopes(
      Region(NamesEntity(kEntity) + Writes("key_keyname", kKeyName)), {},
      TheEntitysKey());
  ProtectKeyList held;
  held.Add(KeyOf(kOtherEntity, kKeyName, kEntityKey));
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = held;
  Preprocessor pp(mgr, diag, std::move(config));
  std::string text = pp.Preprocess(mgr.AddFile("<test>", envelope));
  EXPECT_FALSE(Holds(text, kSealedDesign)) << text;
}

}  // namespace
