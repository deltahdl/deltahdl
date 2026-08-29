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
// The third is not performed at all. #3281 records that: the five names inside
// the value are never separated from the text around them, no library is
// loaded, no function is called, and nothing is reported. Two cases here state
// the consequence rather than the rule -- a licensed model decrypts for a
// reader who was never asked for a licence, and the run says nothing about it.
//
// Which spelling the expression is written in is §34.5.28.1's and is stated in
// test_preprocessor_subclause_34_05_28_01.cpp.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_protect_read.h"
#include "helpers_protect_keys.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
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

// A region reaching the author's own key, with `described` written inside it.
std::string Region(std::string_view described) {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("data_keyowner", kEntity));
  text.append(Writes("data_keyname", kKeyName));
  text.append(described).append(kEncodingSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// The envelope this tool writes for that region.
std::string EnvelopeOf(std::string_view described) {
  std::string envelope = EncryptEnvelopes(Region(described), {}, TheKey());
  EXPECT_FALSE(Holds(envelope, kEncodingSealedDesign)) << envelope;
  return envelope;
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
// is what "output unchanged except for the encryption and encoding" means.
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

// -- What the licence is not consulted for -----------------------------------

// §34.5.28.2 has the tool load the library, call the entry function and refuse
// to decrypt where what comes back does not match. #3281 records that none of
// that happens, and this is what it costs: a reader holding the key reaches the
// design, the licence the author stated deciding nothing.
TEST(ProtectDecryptLicenseDescription, TheDesignIsReachedWithNoLicenceChecked) {
  ReadSource run(EnvelopeOf(kLicense), ReadSource::KeysConfig(TheKey()));
  EXPECT_TRUE(Holds(run.text, kEncodingSealedDesign)) << run.text;
}

// And the run says nothing about it. §34.5.28.2 has an unlicensed tool produce
// an error carrying the value the entry function returned; a tool that called
// no function has no value to carry, and reports neither that nor the fact that
// it never looked.
TEST(ProtectDecryptLicenseDescription, NothingIsReportedAboutTheLicence) {
  ReadSource run(EnvelopeOf(kLicense), ReadSource::KeysConfig(TheKey()));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
}

}  // namespace
