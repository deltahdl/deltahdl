#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kKeyName = "wrapping-2027";
constexpr std::string_view kPublicKey = "acme-public-key-of-2027";

constexpr std::string_view kTheKey = "meridian-trust-wrapping-key";
constexpr std::string_view kAnotherKey = "meridian-trust-key-of-2026";

constexpr std::string_view kDataKeyName = "design-2027";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

constexpr std::string_view kDisagreement =
    "key_public_key and key_keyname designate different keys of the "
    "key_keyowner in effect";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string Encoded(std::string_view key) {
  return EncodeProtectBlock(key, DefaultProtectEncoding());
}

std::string DesignatesByPublicKey(std::string_view key) {
  std::string text = "`pragma protect key_public_key\n";
  text.append(Encoded(key)).append("\n");
  return text;
}

std::string EnvelopeCarrying(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text += "`pragma protect end_protected\n";
  return text;
}

PreprocConfig HoldingBothDesignations(std::string_view under_name,
                                      std::string_view under_public) {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, under_name));
  keys.Add(KeyOf(kEntity, kPublicKey, under_public));
  PreprocConfig config;
  config.protect_keys = keys;
  return config;
}

PreprocConfig HoldingTheNameAlone() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, kTheKey));
  PreprocConfig config;
  config.protect_keys = keys;
  return config;
}

std::string RegionDesignating(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("key_keyowner", kEntity));
  text.append(Writes("data_keyname", kDataKeyName));
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

ProtectKeyList HeldUnderThePublicKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kPublicKey, kTheKey));
  return keys;
}

TEST(ProtectKeyPublicKeyDescription,
     TwoDesignationsReachingTwoKeysAreReported) {
  std::string src = EnvelopeCarrying(Writes("key_keyowner", kEntity) +
                                     Writes("key_keyname", kKeyName) +
                                     DesignatesByPublicKey(kPublicKey));
  PreprocFixture f;
  Preprocess(src, f, HoldingBothDesignations(kTheKey, kAnotherKey));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kDisagreement,
                            LineHolding(src, Encoded(kPublicKey)), "34.5.26"));
}

TEST(ProtectKeyPublicKeyDescription,
     TwoDesignationsReachingOneKeyAreNotReported) {
  std::string src = EnvelopeCarrying(Writes("key_keyowner", kEntity) +
                                     Writes("key_keyname", kKeyName) +
                                     DesignatesByPublicKey(kPublicKey));
  PreprocFixture f;
  Preprocess(src, f, HoldingBothDesignations(kTheKey, kTheKey));
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProtectKeyPublicKeyDescription,
     ADesignationReachingNoHeldKeyLeavesTheOtherAlone) {
  std::string src = EnvelopeCarrying(Writes("key_keyowner", kEntity) +
                                     Writes("key_keyname", kKeyName) +
                                     DesignatesByPublicKey(kPublicKey));
  PreprocFixture f;
  Preprocess(src, f, HoldingTheNameAlone());
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProtectKeyPublicKeyDescription, TheNameWrittenLastCompletesThePair) {
  std::string src = EnvelopeCarrying(Writes("key_keyowner", kEntity) +
                                     DesignatesByPublicKey(kPublicKey) +
                                     Writes("key_keyname", kKeyName));
  PreprocFixture f;
  Preprocess(src, f, HoldingBothDesignations(kAnotherKey, kTheKey));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kDisagreement,
                            LineHolding(src, "`pragma protect key_keyname"),
                            "34.5.26"));
}

TEST(ProtectKeyPublicKeyDescription, AValueOutsideTheSchemeInEffectIsReported) {
  std::string src = EnvelopeCarrying(
      "`pragma protect encoding=(enctype=\"base64\")\n"
      "`pragma protect key_public_key\n"
      "not base64!\n");
  PreprocFixture f;
  Preprocess(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "value is not written in the encoding in effect",
                            LineHolding(src, "not base64!"), "34.5.9.2"));
}

TEST(ProtectKeyPublicKeyDescription, AValueOutsideTheSchemeDesignatesNothing) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile(
      "<test>",
      EnvelopeCarrying("`pragma protect encoding=(enctype=\"base64\")\n"
                       "`pragma protect key_public_key\n"
                       "not base64!\n")));
  EXPECT_TRUE(pp.ProtectKeywords().ValueOf(kKeyPublicKeyKeyword).value.empty());
}

TEST(ProtectKeyPublicKeyDescription, TheDesignationHeadsTheBlockItWasUsedFor) {
  std::string envelope =
      EncryptEnvelopes(RegionDesignating(DesignatesByPublicKey(kPublicKey)), {},
                       HeldUnderThePublicKey());
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, "`pragma protect key_block")) << envelope;
  EXPECT_TRUE(Holds(envelope, "`pragma protect key_public_key")) << envelope;
}

TEST(ProtectKeyPublicKeyDescription, ADesignationAheadOfTheRegionIsUsedToo) {
  std::string src = Writes("key_keyowner", kEntity);
  src.append(DesignatesByPublicKey(kPublicKey));
  src.append("`pragma protect begin\n");
  src.append(Writes("data_keyname", kDataKeyName)).append(kSealedDesign);
  src.append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(src, {}, HeldUnderThePublicKey());
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, "`pragma protect key_block")) << envelope;
}

TEST(ProtectKeyPublicKeyDescription, ABlockReachedByNameCarriesNoPublicKey) {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, kTheKey));
  std::string envelope = EncryptEnvelopes(
      RegionDesignating(Writes("key_keyname", kKeyName)), {}, keys);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, "`pragma protect key_block")) << envelope;
  EXPECT_FALSE(Holds(envelope, "key_public_key")) << envelope;
}

struct LongPublicKeyRun {
  std::string written;
  std::string envelope;

  explicit LongPublicKeyRun(std::string_view encoding_list) {
    const std::string kLongKey(64, 'p');
    ProtectEncoding stated = ParseProtectEncoding(encoding_list);
    written = EncodeProtectValue(kLongKey, stated);
    std::string src = "`pragma protect encoding=";
    src.append(encoding_list).append("\n");
    std::string designation = "`pragma protect key_public_key\n";
    designation.append(written).append("\n");
    src.append(RegionDesignating(designation));
    ProtectKeyList keys;
    keys.Add(KeyOf(kEntity, kLongKey, kTheKey));
    envelope = EncryptEnvelopes(src, {}, keys);
  }
};

TEST(ProtectKeyPublicKeyDescription, AValueLongerThanABase64LineStaysOnOne) {
  LongPublicKeyRun run("(enctype=\"base64\")");
  ASSERT_GT(run.written.size(), 76U);
  EXPECT_TRUE(Holds(run.envelope, "`pragma protect key_public_key\n" +
                                      run.written + "\n`pragma protect"))
      << run.envelope;
}

TEST(ProtectKeyPublicKeyDescription, AStatedLineLengthLeavesTheValueWhole) {
  LongPublicKeyRun run("(enctype=\"base64\", line_length=16)");
  EXPECT_TRUE(Holds(run.envelope, "`pragma protect key_public_key\n" +
                                      run.written + "\n`pragma protect"))
      << run.envelope;
}

TEST(ProtectKeyPublicKeyDescription, ADesignationReachingNoKeyHeadsNoBlock) {
  std::string region = RegionDesignating(DesignatesByPublicKey(kPublicKey));
  EXPECT_EQ(EncryptEnvelopes(region, {}, ProtectKeyList()), region);
}

TEST(ProtectKeyPublicKeyDescription, TheCipherNamedDecidesNothingAboutOpening) {
  std::string envelope =
      EncryptEnvelopes(RegionDesignating(Writes("key_method", kDataMethod) +
                                         DesignatesByPublicKey(kPublicKey)),
                       {}, HeldUnderThePublicKey());
  EXPECT_TRUE(Holds(envelope, Writes("key_method", kDataMethod))) << envelope;
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = HeldUnderThePublicKey();
  Preprocessor pp(mgr, diag, std::move(config));
  EXPECT_TRUE(
      Holds(pp.Preprocess(mgr.AddFile("<test>", envelope)), kSealedDesign));
}

}  // namespace
