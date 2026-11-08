#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kOtherEntity = "cerulean-vault";
constexpr std::string_view kEntitysKeyName = "wrapping-2027";
constexpr std::string_view kOtherEntitysKeyName = "vaulting-2027";
constexpr std::string_view kEntitysKey = "meridian-trust-wrapping-key";
constexpr std::string_view kOtherEntitysKey = "cerulean-vault-vaulting-key";

constexpr std::string_view kUnheldName = "wrapping-1998";

constexpr std::string_view kStrangerEntity = "aegis-custody";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

constexpr std::string_view kNameList =
    "(rotation=\"quarterly\", escrowed_with=\"northwind-escrow\")";

constexpr std::string_view kAuthorsExchangeKey = "the-authors-own-exchange-key";

constexpr std::string_view kKeyHeldUnderTheListsCharacters =
    "meridian-trust-escrowed-key";

constexpr std::string_view kKeyBlockExpression = "`pragma protect key_block\n";

constexpr std::string_view kNoSuchKey =
    "key_keyname names no key held by the key_keyowner in effect";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string Designates(std::string_view entity, std::string_view name) {
  std::string text = Writes("key_keyowner", entity);
  text.append(Writes("key_keyname", name));
  return text;
}

std::string WritesAsSpelled(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=").append(value).append("\n");
  return text;
}

ProtectKeyList KeysOfBothEntities() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kEntitysKeyName, kEntitysKey));
  keys.Add(KeyOf(kOtherEntity, kOtherEntitysKeyName, kOtherEntitysKey));
  return keys;
}

PreprocConfig HoldingBothLists() {
  PreprocConfig config;
  config.protect_keys = KeysOfBothEntities();
  return config;
}

std::string Region(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

TEST(ProtectKeyKeynameDescription, ANameOutsideTheEntitysListIsReported) {
  std::string src = Designates(kEntity, kUnheldName);
  PreprocFixture f;
  Preprocess(src, f, HoldingBothLists());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "key_keyname"), "34.5.25"));
}

TEST(ProtectKeyKeynameDescription, ANameOfAnotherEntitysKeyIsReported) {
  std::string src = Designates(kEntity, kOtherEntitysKeyName);
  PreprocFixture f;
  Preprocess(src, f, HoldingBothLists());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "key_keyname"), "34.5.25"));
}

TEST(ProtectKeyKeynameDescription, ANameInTheEntitysListIsNotReported) {
  PreprocFixture f;
  Preprocess(Designates(kEntity, kEntitysKeyName), f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProtectKeyKeynameDescription, TheEntityDecidesWhichListTheNameIsIn) {
  PreprocFixture f;
  Preprocess(Designates(kOtherEntity, kOtherEntitysKeyName), f,
             HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProtectKeyKeynameDescription, AnEntityWithNoListDrawsNoReport) {
  PreprocFixture f;
  Preprocess(Designates(kStrangerEntity, kUnheldName), f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProtectKeyKeynameDescription, ThePairSelectsTheKeyTheBlockIsOpenedWith) {
  ProtectKeyList keys = KeysOfBothEntities();
  EXPECT_EQ(ReadKeywordScope(Designates(kEntity, kEntitysKeyName))
                .KeyBlockKeyReached(keys),
            kEntitysKey);
  EXPECT_EQ(ReadKeywordScope(Designates(kOtherEntity, kOtherEntitysKeyName))
                .KeyBlockKeyReached(keys),
            kOtherEntitysKey);
}

TEST(ProtectKeyKeynameDescription, TheHalvesOfOnePairReachNothingCrossed) {
  ProtectKeyList keys = KeysOfBothEntities();
  EXPECT_TRUE(ReadKeywordScope(Designates(kEntity, kOtherEntitysKeyName))
                  .KeyBlockKeyReached(keys)
                  .empty());
}

TEST(ProtectKeyKeynameDescription, TheNameStandsAsCleartextOnTheEnvelope) {
  std::string envelope = EncryptEnvelopes(
      Region(Designates(kEntity, kEntitysKeyName)), {}, KeysOfBothEntities());
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, Writes("key_keyname", kEntitysKeyName)))
      << envelope;
}

TEST(ProtectKeyKeynameDescription,
     TheNameStandsAsCleartextInTheBlocksOwnDirective) {
  std::string envelope = EncryptEnvelopes(
      Region(Designates(kEntity, kEntitysKeyName)), {}, KeysOfBothEntities());
  EXPECT_TRUE(Holds(envelope, "`pragma protect key_block")) << envelope;
  EXPECT_EQ(TimesWritten(envelope, Writes("key_keyname", kEntitysKeyName)), 2U)
      << envelope;
}

TEST(ProtectKeyKeynameDescription, ARegionNamingAKeyNobodyHoldsIsSealedByNone) {
  std::string region = Region(Designates(kEntity, kUnheldName));
  EXPECT_EQ(EncryptEnvelopes(region, {}, KeysOfBothEntities()), region);
}

TEST(ProtectKeyKeynameDescription, AListPutsNoKeyNameOnTheEnvelope) {
  std::string envelope = EncryptEnvelopes(
      Region(WritesAsSpelled("key_keyname", kNameList)), kAuthorsExchangeKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_EQ(TimesWritten(envelope, "key_keyname="), 0U) << envelope;
}

TEST(ProtectKeyKeynameDescription, AStringNamesTheKeyTheEnvelopeOutputs) {
  std::string envelope = EncryptEnvelopes(
      Region(Writes("key_keyname", kEntitysKeyName)), kAuthorsExchangeKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, Writes("key_keyname", kEntitysKeyName)))
      << envelope;
}

TEST(ProtectKeyKeynameDescription,
     AListLeavesTheStringWrittenBeforeItStanding) {
  std::string envelope =
      EncryptEnvelopes(Region(Writes("key_keyname", kEntitysKeyName) +
                              WritesAsSpelled("key_keyname", kNameList)),
                       kAuthorsExchangeKey);
  EXPECT_TRUE(Holds(envelope, Writes("key_keyname", kEntitysKeyName)))
      << envelope;
  EXPECT_FALSE(Holds(envelope, kNameList)) << envelope;
}

ProtectKeyList KeysHeldUnderBothSpellings() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kEntitysKeyName, kEntitysKey));
  keys.Add(KeyOf(kEntity, kNameList, kKeyHeldUnderTheListsCharacters));
  return keys;
}

TEST(ProtectKeyKeynameDescription, AListAsksForNoKeyBlock) {
  std::string region = Region(Writes("key_keyowner", kEntity) +
                              WritesAsSpelled("key_keyname", kNameList));
  std::string envelope =
      EncryptEnvelopes(region, {}, KeysHeldUnderBothSpellings());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockExpression), 0U) << envelope;
}

TEST(ProtectKeyKeynameDescription, AStringAsksForTheOneKeyBlock) {
  std::string region = Region(Designates(kEntity, kEntitysKeyName));
  std::string envelope =
      EncryptEnvelopes(region, {}, KeysHeldUnderBothSpellings());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockExpression), 1U) << envelope;
}

TEST(ProtectKeyKeynameDescription, AHeldDataKeyTravelsInTheNamedKeysBlock) {
  std::string region = Writes("data_keyowner", kOtherEntity) +
                       Writes("data_keyname", kOtherEntitysKeyName) +
                       Designates(kEntity, kEntitysKeyName) +
                       Writes("key_method", "des-cbc") + Region("");
  std::string envelope = EncryptEnvelopes(region, {}, KeysOfBothEntities());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockExpression), 1U) << envelope;
  EXPECT_NE(envelope.find("`pragma protect begin_protected\n"),
            std::string::npos)
      << envelope;
  EXPECT_GE(TimesWritten(envelope, "`pragma protect key_method=\"des-cbc\"\n"),
            2U)
      << envelope;
}

struct SigningRun {
  PreprocFixture f;
  std::string text;

  explicit SigningRun(const std::string& src)
      : text(EncryptEnvelopes(src, {}, KeysOfBothEntities(), &f.diag,
                              f.mgr.AddFile("<test>", src))) {}
};

TEST(ProtectKeyKeynameEncryptionInput, AnUnheldNameIsReportedWhenSealing) {
  SigningRun run(Region(Designates(kEntity, kUnheldName)));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNoSuchKey, 3, "34.5.25"))
      << run.text;
}

TEST(ProtectKeyKeynameEncryptionInput, AHeldNameIsSealedInSilence) {
  SigningRun run(Region(Designates(kEntity, kEntitysKeyName)));
  EXPECT_FALSE(run.f.diag.HasErrors()) << run.text;
}

TEST(ProtectKeyKeynameEncryptionInput, ANameUnderAnUnheldEntityIsNotReported) {
  SigningRun run(Region(Designates(kStrangerEntity, kUnheldName)));
  EXPECT_EQ(run.f.diag.ErrorCount(), 1U) << run.text;
  EXPECT_TRUE(
      ReportedError(run.f.diag.Diagnostics(),
                    "protect pragma encryption envelope has no key to be "
                    "encrypted under, so it is written out unencrypted",
                    1, "34.3.1"));
}

}  // namespace
