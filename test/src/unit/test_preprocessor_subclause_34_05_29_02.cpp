// §34.5.29.2 runtime_license, Description.
//
// The subclause states three things.
//
//   ENCRYPTION INPUT: the expression will typically be found inside a begin-end
//   pair in the original cleartext, so that it is encrypted in the output the
//   author ships.
//
//   ENCRYPTION OUTPUT: it is output unchanged except for the encryption and
//   encoding every other line of cleartext in that pair receives.
//
//   DECRYPTION INPUT: on meeting the expression in an encrypted model, and
//   before executing it, the tool loads the library the value names, calls the
//   entry function with the feature string, and compares what comes back
//   against the match value. Where the tool is not licensed, execution shall
//   not begin, and the report carries the value the function returned. An exit
//   function, where one is named, is called before the tool exits.
//
// The first two are stated already, and stated for this keyword rather than for
// a keyword like it.
// EnvelopeEncryption.AnExpressionInsideTheEnvelopeIsEncrypted WithIt and
// .TheSameExpressionOutsideTheEnvelopeIsNotEncrypted in
// test_preprocessor_subclause_34_03_01a.cpp write a runtime_license inside a
// region and outside one, and hold the recovered block to equalling the
// expression and the design exactly -- which is what "unchanged except for the
// encryption" asks, said more precisely than a search of the text could say it.
// Restating them here under this subclause's name would add a second copy of a
// claim already made and nothing else.
//
// What those two leave open is the first case below. They show the expression
// treated one way inside a region and another way outside it, which is
// consistent with a tool that lifts nothing out of a region at all. §34.5.5 has
// the author's name lifted out and written in the clear, so a licence and a
// name written in the same place coming out differently is what says the
// subclause decided this rather than the position.
//
// The third rule is where the two licence keywords part: §34.5.28.2's check
// stands before the decrypted text is processed, which is inside the
// preprocessor, and this one stands before the model is executed, which is
// past it. So Preprocessor::ApplyLicense
// (src/preprocessor/preprocessor_protect_license.cpp) records each such
// expression it meets in an encrypted model, and the run asks them before
// synthesis or simulation begins (RuntimeLicensesGranted in
// src/driver/protect_license_libraries.h, whose cases are in
// test_simulator_subclause_34_05_29_02.cpp). The cases after the first state
// what the reading records.

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

// The licence a region states, written as §34.5.29.1 spells it.
constexpr std::string_view kLicense =
    "`pragma protect runtime_license=(library=\"liblic.so\", "
    "entry=\"checkout\", feature=\"simulate\", match=1)\n";

// The library the licence names, which is the part of the value a reader
// looking at what the tool produced could pick out.
constexpr std::string_view kLibrary = "liblic.so";

// The name the author writes beside it, which §34.5.5 does lift out.
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

// §34.5.5 has the author's name lifted out of the region and written in the
// clear beside the block; §34.5.29.2 has the licence encrypted with everything
// else the region held. The two are written in one region here, so what
// separates them is the subclause each is defined by and not where either
// stands.
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

// The characters recording one envelope's sealed region: the line beneath its
// data_block expression. §34.5.15.1 spells that expression as the keyword
// standing alone and §34.5.15.2 has the block begin on the next line in the
// file (issue #3272).
std::string DataBlockOf(const std::string& envelope) {
  constexpr std::string_view kAnnouncement = "`pragma protect data_block\n";
  size_t opens = envelope.find(kAnnouncement);
  EXPECT_NE(opens, std::string::npos) << envelope;
  size_t from = opens + kAnnouncement.size();
  return envelope.substr(from, envelope.find('\n', from) - from);
}

// The envelope this tool writes for a region stating the licence.
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

// The licence met in the encrypted model is recorded for the run that executes
// it, at the licence's own line inside the recovered text, that being what the
// reading of that text numbers from.
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

// The model is read all the same. Execution is what the licence guards, and
// reading the model is not executing it, so nothing is reported and the design
// reaches the step after.
TEST(ProtectRuntimeLicenseDescription, TheModelIsReadAllTheSame) {
  ReadSource run(EnvelopeStatingTheLicence(), ReadSource::KeysConfig(TheKey()));
  EXPECT_TRUE(Holds(run.text, kSealedDesign)) << run.text;
  EXPECT_TRUE(run.diag.Diagnostics().empty());
}

// A licence in cleartext the tool is about to encrypt is the ENCRYPTION INPUT
// case, met in no encrypted model, so it is not recorded.
TEST(ProtectRuntimeLicenseDescription, ALicenceInCleartextIsNotRecorded) {
  ReadSource run{std::string(kLicense)};
  EXPECT_TRUE(run.pp.RuntimeLicenses().empty());
}

}  // namespace
