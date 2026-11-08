#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "fixture_protect_read.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kLicense =
    "`pragma protect runtime_license=(library=\"liblic.so\", "
    "entry=\"checkout\", feature=\"simulate\", match=1)\n";

constexpr std::string_view kLibrary = "liblic.so";

constexpr std::string_view kAuthor = "acme-semiconductor";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kKeyName = "design-2027";
constexpr std::string_view kTheKey = "meridian-trust-design-key";

ProtectKeyList TheKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, kTheKey));
  return keys;
}

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

TEST(ProtectRuntimeLicenseDescription,
     TheAuthorIsLiftedOutWhereTheLicenceIsNot) {
  std::string region = "`pragma protect begin\n";
  region.append(Writes("data_keyowner", kEntity));
  region.append(Writes("data_keyname", kKeyName));
  region.append(kLicense).append(Writes("author", kAuthor));
  region.append(kSealedDesign).append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(region, {}, TheKey());
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, kAuthor)) << envelope;
  EXPECT_FALSE(Holds(envelope, kLibrary)) << envelope;
}

std::string DataBlockOf(const std::string& envelope) {
  constexpr std::string_view kAnnouncement = "`pragma protect data_block\n";
  size_t opens = envelope.find(kAnnouncement);
  EXPECT_NE(opens, std::string::npos) << envelope;
  size_t from = opens + kAnnouncement.size();
  return envelope.substr(from, envelope.find('\n', from) - from);
}

std::string EnvelopeStatingTheLicence() {
  std::string region = "`pragma protect begin\n";
  region.append(Writes("data_keyowner", kEntity));
  region.append(Writes("data_keyname", kKeyName));
  region.append(kLicense).append(kSealedDesign);
  region.append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(region, {}, TheKey());
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  return envelope;
}

TEST(ProtectRuntimeLicenseDescription, TheLicenceIsRecordedForTheRun) {
  std::string envelope = EnvelopeStatingTheLicence();
  std::string cleartext;
  ASSERT_TRUE(
      DecryptProtectedRegion(DataBlockOf(envelope), kTheKey, &cleartext));
  ReadSource run(envelope, ReadSource::KeysConfig(TheKey()));
  ASSERT_EQ(run.pp.RuntimeLicenses().size(), 1U);
  const ProtectRuntimeLicense& recorded = run.pp.RuntimeLicenses()[0];
  EXPECT_EQ(recorded.license.library, kLibrary);
  EXPECT_EQ(recorded.license.entry, "checkout");
  EXPECT_EQ(recorded.license.feature, "simulate");
  EXPECT_EQ(recorded.license.match, 1U);
  EXPECT_EQ(recorded.loc.line, LineHolding(cleartext, kLicense));
}

TEST(ProtectRuntimeLicenseDescription, TheModelIsReadAllTheSame) {
  ReadSource run(EnvelopeStatingTheLicence(), ReadSource::KeysConfig(TheKey()));
  EXPECT_TRUE(Holds(run.text, kSealedDesign)) << run.text;
  EXPECT_TRUE(run.diag.Diagnostics().empty());
}

TEST(ProtectRuntimeLicenseDescription, ALicenceInCleartextIsNotRecorded) {
  ReadSource run{std::string(kLicense)};
  EXPECT_TRUE(run.pp.RuntimeLicenses().empty());
}

}  // namespace
