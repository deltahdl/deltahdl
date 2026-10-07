// §34.5.28.2 decrypt_license, Description.
//
// The subclause states three things.
//
//   ENCRYPTION INPUT: the expression will typically be found inside a begin-end
//   pair in the original cleartext, so that it is encrypted in the output the
//   author ships.
//
//   ENCRYPTION OUTPUT: it is output unchanged except for the encryption and
//   encoding every other line of cleartext in that pair receives. Typically it
//   goes out in the data block.
//
//   DECRYPTION INPUT: on meeting the expression in an encrypted model, and
//   before processing the decrypted text, the tool loads the library the value
//   names, calls the entry function in it with the feature string, and compares
//   what comes back against the match value. Where they differ the tool is not
//   licensed: no decryption is performed and the report carries the value the
//   function returned. An exit function, where one is named, is called before
//   the tool exits so the licence is released.
//
// The first two are what this file states. They are one rule seen from two
// sides: the expression is not lifted out of the region the way the keywords
// naming a key are, so it rides into the data block with the design and comes
// back with it.
//
// The third is Preprocessor::ApplyLicense's
// (src/preprocessor/preprocessor_protect_license.cpp). The preprocessor loads
// no object code itself, so the asking is the configuration's ask_license,
// which a run supplies (src/driver/protect_license_libraries.h) and which the
// cases here answer with a stub: what the entry function returned, or why it
// was not called. The cases after the encryption ones state what the reading
// does with each answer -- a match decrypts, anything else is reported with
// the value and decrypts nothing, an absent match is held to 0, and a licence
// in cleartext asks nothing.
//
// Which spelling the expression is written in is §34.5.28.1's and is stated in
// test_preprocessor_subclause_34_05_28_01.cpp.

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

// The licence a region states, written as §34.5.28.1 spells it.
constexpr std::string_view kLicense =
    "`pragma protect decrypt_license=(library=\"liblic.so\", "
    "entry=\"checkout\", feature=\"decrypt\", match=1)\n";

// The library the licence names, which is the one thing in the value a reader
// looking at the output could pick out.
constexpr std::string_view kLibrary = "liblic.so";

constexpr std::string_view kEncodingSealedDesign =
    "module sealed_m; endmodule\n";

// The entity whose key opens the region, and the key itself.
constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kKeyName = "design-2027";
constexpr std::string_view kTheKey = "meridian-trust-design-key";

ProtectKeyList TheKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, kTheKey));
  return keys;
}

// The characters recording one envelope's sealed region: the line beneath its
// data_block expression. §34.5.15.1 spells that expression as the keyword
// standing alone and §34.5.15.2 has the block begin on the next line in the
// file (issue #3272).
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

// A region reaching the author's own key, with `described` written inside it
// ahead of `design`.
std::string Region(std::string_view described,
                   std::string_view design = kEncodingSealedDesign) {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("data_keyowner", kEntity));
  text.append(Writes("data_keyname", kKeyName));
  text.append(described).append(design);
  text.append("`pragma protect end\n");
  return text;
}

// The envelope this tool writes for that region.
std::string EnvelopeOf(std::string_view described,
                       std::string_view design = kEncodingSealedDesign) {
  std::string envelope =
      EncryptEnvelopes(Region(described, design), {}, TheKey());
  EXPECT_FALSE(Holds(envelope, design)) << envelope;
  return envelope;
}

// The licences a stub asking was handed, in the order it was handed them.
struct Asked {
  std::vector<ProtectLicense> licenses;
};

// A reading holding the author's key whose licences are answered with
// `answer`, each one asked being kept in `asked`.
PreprocConfig Answering(const ProtectLicenseAnswer& answer, Asked* asked) {
  PreprocConfig config = ReadSource::KeysConfig(TheKey());
  config.ask_license = [answer, asked](const ProtectLicense& license) {
    asked->licenses.push_back(license);
    return answer;
  };
  return config;
}

// An entry function that was called and returned `value`.
ProtectLicenseAnswer Returning(int64_t value) {
  ProtectLicenseAnswer answer;
  answer.called = true;
  answer.returned = value;
  return answer;
}

// The line of the recovered text the licence stands on, which is what the
// reading of that text numbers a report about it from.
uint32_t LicenceLine(const std::string& envelope, std::string_view license) {
  std::string cleartext;
  EXPECT_TRUE(DecryptProtectedRegion(EncodingDataBlockOf(envelope), kTheKey,
                                     &cleartext));
  return LineHolding(cleartext, license);
}

// -- The expression rides into the block -------------------------------------

// §34.5.28.2: the expression is output unchanged except for the encryption and
// encoding every other line of cleartext in the pair receives. So it is gone
// from what stands in the clear: an expression the tool lifted out would be
// readable beside the block, and this one is not.
TEST(ProtectDecryptLicenseDescription, TheLicenceIsNowhereInTheClear) {
  std::string envelope = EnvelopeOf(kLicense);
  EXPECT_FALSE(Holds(envelope, "decrypt_license")) << envelope;
  EXPECT_FALSE(Holds(envelope, kLibrary)) << envelope;
}

// The other side of the same rule: it went into the block rather than being
// dropped. The block recovers to the expression and the design together, which
// is what an output changed by nothing but its encryption and encoding means.
//
// What is opened here is the block rather than the envelope, because a reading
// that opens an envelope goes on to read what came out of it: the recovered
// text is source, and a protect pragma directive in it is consumed the way one
// in any source is. The block is where the expression stands unchanged, and it
// is the only place it could stand and still be encrypted.
TEST(ProtectDecryptLicenseDescription,
     TheBlockRecoversToTheLicenceAndTheDesign) {
  std::string cleartext;
  ASSERT_TRUE(DecryptProtectedRegion(EncodingDataBlockOf(EnvelopeOf(kLicense)),
                                     kTheKey, &cleartext));
  EXPECT_TRUE(Holds(cleartext, kLicense)) << cleartext;
  EXPECT_TRUE(Holds(cleartext, kEncodingSealedDesign)) << cleartext;
}

// The contrast that says the region decided this. §34.5.5 has the author's name
// lifted out of the block and written in the clear beside it, and the licence
// written in the same place is not: one subclause makes an exception of its
// keyword and this one does not.
TEST(ProtectDecryptLicenseDescription,
     TheAuthorIsLiftedOutWhereTheLicenceIsNot) {
  std::string envelope = EnvelopeOf(
      std::string(kLicense).append(Writes("author", "acme-semiconductor")));
  EXPECT_TRUE(Holds(envelope, "acme-semiconductor")) << envelope;
  EXPECT_FALSE(Holds(envelope, kLibrary)) << envelope;
}

// A licence written outside the region is text of the source like any other, so
// it is neither encrypted nor lifted: it stands where it was written. Without
// this the cases above would hold of a reading that dropped the expression
// wherever it found it.
TEST(ProtectDecryptLicenseDescription, ALicenceOutsideTheRegionStaysWhereItIs) {
  std::string source = std::string(kLicense).append(Region(""));
  std::string envelope = EncryptEnvelopes(source, {}, TheKey());
  EXPECT_TRUE(Holds(envelope, kLibrary)) << envelope;
}

// -- What the licence is asked and what its answer decides -------------------

// §34.5.28.2: on meeting the expression in an encrypted model the tool loads
// the library the value names and calls the entry function in it, passing the
// feature string. The one asking made is for the three the value wrote.
TEST(ProtectDecryptLicenseDescription, TheLibraryIsAskedAboutTheFeature) {
  Asked asked;
  ReadSource run(EnvelopeOf(kLicense), Answering(Returning(1), &asked));
  ASSERT_EQ(asked.licenses.size(), 1U);
  EXPECT_EQ(asked.licenses[0].library, "liblic.so");
  EXPECT_EQ(asked.licenses[0].entry, "checkout");
  EXPECT_EQ(asked.licenses[0].feature, "decrypt");
}

// A returned value equal to the match value licenses the tool, so the model is
// decrypted and its design reaches the step after, with nothing reported.
TEST(ProtectDecryptLicenseDescription, AMatchingAnswerDecryptsTheModel) {
  Asked asked;
  ReadSource run(EnvelopeOf(kLicense), Answering(Returning(1), &asked));
  EXPECT_TRUE(Holds(run.text, kEncodingSealedDesign)) << run.text;
  EXPECT_TRUE(run.diag.Diagnostics().empty());
}

// Any other value leaves the tool unlicensed, and the error includes the value
// the entry function returned. The report stands at the licence's own line in
// the recovered text.
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

// And no decryption is performed: nothing of the model reaches the step after.
TEST(ProtectDecryptLicenseDescription, AnotherAnswerDecryptsNothing) {
  Asked asked;
  ReadSource run(EnvelopeOf(kLicense), Answering(Returning(7), &asked));
  EXPECT_FALSE(Holds(run.text, kEncodingSealedDesign)) << run.text;
}

// A licence writing no match value is held to 0, the value the NOTE closing the
// subclause has a forged library return to avoid the check. An entry function
// returning 0 licenses the tool.
constexpr std::string_view kLicenseWithoutMatch =
    "`pragma protect decrypt_license=(library=\"liblic.so\", "
    "entry=\"checkout\", feature=\"decrypt\")\n";

TEST(ProtectDecryptLicenseDescription, NoMatchValueIsAnsweredByZero) {
  Asked asked;
  ReadSource run(EnvelopeOf(kLicenseWithoutMatch),
                 Answering(Returning(0), &asked));
  EXPECT_TRUE(Holds(run.text, kEncodingSealedDesign)) << run.text;
}

// And one returning anything else does not.
TEST(ProtectDecryptLicenseDescription, NoMatchValueRefusesAnyOtherAnswer) {
  Asked asked;
  ReadSource run(EnvelopeOf(kLicenseWithoutMatch),
                 Answering(Returning(1), &asked));
  EXPECT_FALSE(Holds(run.text, kEncodingSealedDesign)) << run.text;
}

// An entry function that could not be called returned no value that could
// compare equal, so the tool is unlicensed and the error says why.
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

// A reading given no way to ask loads no library, so it is unlicensed as well:
// the model stays sealed rather than being decrypted unasked.
TEST(ProtectDecryptLicenseDescription, AReadingThatCannotAskDecryptsNothing) {
  ReadSource run(EnvelopeOf(kLicense), ReadSource::KeysConfig(TheKey()));
  EXPECT_FALSE(Holds(run.text, kEncodingSealedDesign)) << run.text;
}

// The refusal belongs to the envelope that stated the licence. An envelope
// after it states none, so its design is decrypted all the same.
TEST(ProtectDecryptLicenseDescription, TheRefusalEndsWithItsEnvelope) {
  constexpr std::string_view kLaterDesign = "module later_m; endmodule\n";
  Asked asked;
  ReadSource run(EnvelopeOf(kLicense) + EnvelopeOf("", kLaterDesign),
                 Answering(Returning(7), &asked));
  EXPECT_TRUE(Holds(run.text, kLaterDesign)) << run.text;
}

// The control on where the question is put. §34.5.28.2 puts it on meeting the
// expression in an encrypted model, so a licence standing in cleartext the
// tool is about to encrypt asks nothing of this run: that is the ENCRYPTION
// INPUT case the subclause opens with, and the expression speaks to whoever
// reads the shipped output rather than to whoever wrote it.
TEST(ProtectDecryptLicenseDescription, ALicenceInCleartextIsNotAsked) {
  Asked asked;
  ReadSource run(std::string(kLicense), Answering(Returning(7), &asked));
  EXPECT_TRUE(asked.licenses.empty());
  EXPECT_TRUE(run.diag.Diagnostics().empty());
}

}  // namespace
