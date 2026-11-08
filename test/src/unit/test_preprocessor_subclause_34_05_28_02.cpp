#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_protect_read.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_license.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kLicense =
    "`pragma protect decrypt_license=(library=\"liblic.so\", "
    "entry=\"checkout\", feature=\"decrypt\", match=1)\n";

constexpr std::string_view kLibrary = "liblic.so";

constexpr std::string_view kEncodingSealedDesign =
    "module sealed_m; endmodule\n";

constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kKeyName = "design-2027";
constexpr std::string_view kTheKey = "meridian-trust-design-key";

ProtectKeyList TheKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, kTheKey));
  return keys;
}

std::string EncodingDataBlockOf(const std::string& envelope) {
  constexpr std::string_view kAnnouncement = "`pragma protect data_block\n";
  size_t opens = envelope.find(kAnnouncement);
  EXPECT_NE(opens, std::string::npos) << envelope;
  size_t from = opens + kAnnouncement.size();
  return envelope.substr(from, envelope.find('\n', from) - from);
}

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

std::string Region(std::string_view described,
                   std::string_view design = kEncodingSealedDesign) {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("data_keyowner", kEntity));
  text.append(Writes("data_keyname", kKeyName));
  text.append(described).append(design);
  text.append("`pragma protect end\n");
  return text;
}

std::string EnvelopeOf(std::string_view described,
                       std::string_view design = kEncodingSealedDesign) {
  std::string envelope =
      EncryptEnvelopes(Region(described, design), {}, TheKey());
  EXPECT_FALSE(Holds(envelope, design)) << envelope;
  return envelope;
}

struct Asked {
  std::vector<ProtectLicense> licenses;
};

PreprocConfig Answering(const ProtectLicenseAnswer& answer, Asked* asked) {
  PreprocConfig config = ReadSource::KeysConfig(TheKey());
  config.ask_license = [answer, asked](const ProtectLicense& license) {
    asked->licenses.push_back(license);
    return answer;
  };
  return config;
}

ProtectLicenseAnswer Returning(int64_t value) {
  ProtectLicenseAnswer answer;
  answer.called = true;
  answer.returned = value;
  return answer;
}

uint32_t LicenceLine(const std::string& envelope, std::string_view license) {
  std::string cleartext;
  EXPECT_TRUE(DecryptProtectedRegion(EncodingDataBlockOf(envelope), kTheKey,
                                     &cleartext));
  return LineHolding(cleartext, license);
}

TEST(ProtectDecryptLicenseDescription, TheLicenceIsNowhereInTheClear) {
  std::string envelope = EnvelopeOf(kLicense);
  EXPECT_FALSE(Holds(envelope, "decrypt_license")) << envelope;
  EXPECT_FALSE(Holds(envelope, kLibrary)) << envelope;
}

TEST(ProtectDecryptLicenseDescription,
     TheBlockRecoversToTheLicenceAndTheDesign) {
  std::string cleartext;
  ASSERT_TRUE(DecryptProtectedRegion(EncodingDataBlockOf(EnvelopeOf(kLicense)),
                                     kTheKey, &cleartext));
  EXPECT_TRUE(Holds(cleartext, kLicense)) << cleartext;
  EXPECT_TRUE(Holds(cleartext, kEncodingSealedDesign)) << cleartext;
}

TEST(ProtectDecryptLicenseDescription,
     TheAuthorIsLiftedOutWhereTheLicenceIsNot) {
  std::string envelope = EnvelopeOf(
      std::string(kLicense).append(Writes("author", "acme-semiconductor")));
  EXPECT_TRUE(Holds(envelope, "acme-semiconductor")) << envelope;
  EXPECT_FALSE(Holds(envelope, kLibrary)) << envelope;
}

TEST(ProtectDecryptLicenseDescription, ALicenceOutsideTheRegionStaysWhereItIs) {
  std::string source = std::string(kLicense).append(Region(""));
  std::string envelope = EncryptEnvelopes(source, {}, TheKey());
  EXPECT_TRUE(Holds(envelope, kLibrary)) << envelope;
}

TEST(ProtectDecryptLicenseDescription, TheLibraryIsAskedAboutTheFeature) {
  Asked asked;
  ReadSource run(EnvelopeOf(kLicense), Answering(Returning(1), &asked));
  ASSERT_EQ(asked.licenses.size(), 1U);
  EXPECT_EQ(asked.licenses[0].library, "liblic.so");
  EXPECT_EQ(asked.licenses[0].entry, "checkout");
  EXPECT_EQ(asked.licenses[0].feature, "decrypt");
}

TEST(ProtectDecryptLicenseDescription, AMatchingAnswerDecryptsTheModel) {
  Asked asked;
  ReadSource run(EnvelopeOf(kLicense), Answering(Returning(1), &asked));
  EXPECT_TRUE(Holds(run.text, kEncodingSealedDesign)) << run.text;
  EXPECT_TRUE(run.diag.Diagnostics().empty());
}

TEST(ProtectDecryptLicenseDescription, AnotherAnswerIsReportedWithItsValue) {
  std::string envelope = EnvelopeOf(kLicense);
  Asked asked;
  ReadSource run(envelope, Answering(Returning(7), &asked));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma decrypt_license entry function \"checkout\" in "
      "\"liblic.so\" returned 7 for feature \"decrypt\", not the match value "
      "1, so this tool is not licensed to decrypt the model",
      LicenceLine(envelope, kLicense), "34.5.28.2"));
}

TEST(ProtectDecryptLicenseDescription, AnotherAnswerDecryptsNothing) {
  Asked asked;
  ReadSource run(EnvelopeOf(kLicense), Answering(Returning(7), &asked));
  EXPECT_FALSE(Holds(run.text, kEncodingSealedDesign)) << run.text;
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma decrypt_license entry function \"checkout\" in "
      "\"liblic.so\" returned 7 for feature \"decrypt\", not the match value 1",
      3, "34.5.28.2"));
}

TEST(ProtectDecryptLicenseDescription, ARefusedModelDefinesNothing) {
  std::string src =
      EnvelopeOf("`define SECRET_MODE 1\n" + std::string(kLicense));
  src.append("`ifdef SECRET_MODE\nleaked\n`endif\n");
  Asked asked;
  ReadSource run(src, Answering(Returning(7), &asked));
  EXPECT_FALSE(Holds(run.text, "leaked")) << run.text;
  EXPECT_EQ(asked.licenses.size(), 1U);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma decrypt_license entry function \"checkout\" in "
      "\"liblic.so\" returned 7 for feature \"decrypt\", not the match value 1",
      4, "34.5.28.2"));
}

constexpr std::string_view kLicenseWithoutMatch =
    "`pragma protect decrypt_license=(library=\"liblic.so\", "
    "entry=\"checkout\", feature=\"decrypt\")\n";

TEST(ProtectDecryptLicenseDescription, NoMatchValueIsAnsweredByZero) {
  Asked asked;
  ReadSource run(EnvelopeOf(kLicenseWithoutMatch),
                 Answering(Returning(0), &asked));
  EXPECT_TRUE(Holds(run.text, kEncodingSealedDesign)) << run.text;
}

TEST(ProtectDecryptLicenseDescription, NoMatchValueRefusesAnyOtherAnswer) {
  Asked asked;
  ReadSource run(EnvelopeOf(kLicenseWithoutMatch),
                 Answering(Returning(1), &asked));
  EXPECT_FALSE(Holds(run.text, kEncodingSealedDesign)) << run.text;
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma decrypt_license entry function \"checkout\" in "
      "\"liblic.so\" returned 1 for feature \"decrypt\", not the match value 0",
      3, "34.5.28.2"));
}

TEST(ProtectDecryptLicenseDescription, AnUncalledEntryFunctionIsReported) {
  std::string envelope = EnvelopeOf(kLicense);
  ProtectLicenseAnswer unloaded;
  unloaded.why_not_called = "liblic.so: cannot open shared object file";
  Asked asked;
  ReadSource run(envelope, Answering(unloaded, &asked));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma decrypt_license entry function \"checkout\" in "
      "\"liblic.so\" was not called for feature \"decrypt\": liblic.so: "
      "cannot open shared object file, so this tool is not licensed to "
      "decrypt the model",
      LicenceLine(envelope, kLicense), "34.5.28.2"));
}

TEST(ProtectDecryptLicenseDescription, AReadingThatCannotAskDecryptsNothing) {
  ReadSource run(EnvelopeOf(kLicense), ReadSource::KeysConfig(TheKey()));
  EXPECT_FALSE(Holds(run.text, kEncodingSealedDesign)) << run.text;
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma decrypt_license entry function \"checkout\" in "
      "\"liblic.so\" was not called for feature \"decrypt\"",
      3, "34.5.28.2"));
}

TEST(ProtectDecryptLicenseDescription, TheRefusalEndsWithItsEnvelope) {
  constexpr std::string_view kLaterDesign = "module later_m; endmodule\n";
  Asked asked;
  ReadSource run(EnvelopeOf(kLicense) + EnvelopeOf("", kLaterDesign),
                 Answering(Returning(7), &asked));
  EXPECT_TRUE(Holds(run.text, kLaterDesign)) << run.text;
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma decrypt_license entry function \"checkout\" in "
      "\"liblic.so\" returned 7 for feature \"decrypt\", not the match value 1",
      3, "34.5.28.2"));
}

TEST(ProtectDecryptLicenseDescription, ALicenceInCleartextIsNotAsked) {
  Asked asked;
  ReadSource run(std::string(kLicense), Answering(Returning(7), &asked));
  EXPECT_TRUE(asked.licenses.empty());
  EXPECT_TRUE(run.diag.Diagnostics().empty());
}

TEST(ProtectDecryptLicenseDescription, AMalformedLicenceIsReportedNotAsked) {
  constexpr std::string_view kMalformed =
      "`pragma protect decrypt_license=(library=\"liblic.so\")\n";
  std::string envelope = EnvelopeOf(kMalformed);
  Asked asked;
  ReadSource run(envelope, Answering(Returning(1), &asked));
  EXPECT_TRUE(asked.licenses.empty());
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "protect pragma decrypt_license expression is "
                            "written as a library, an entry and a feature, "
                            "each against a string",
                            LicenceLine(envelope, "decrypt_license"),
                            "34.5.28.1"));
}

}  // namespace
