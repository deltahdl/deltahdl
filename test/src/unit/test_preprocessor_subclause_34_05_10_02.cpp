// §34.5.10.2 data_keyowner, Description.
//
// The subclause says four things about the keyword §34.5.10.1 spells.
//
//   It names the legal entity or tool that provided the keys used to encrypt
//   and decrypt the data, and it permits a third-party key, distinct from one
//   associated with either author or encrypt_agent.
//
//   An encrypting tool uses its value to select the key that encrypts the
//   data_block.
//
//   The values written against data_keyname, data_decrypt_key and
//   data_public_key are unique for the entity it names.
//
//   It is unchanged in the output file, except where a digital signature is
//   used, in which case it is encrypted with the key_method and placed in a
//   key_block.
//
// The syntax file beside this one covers what spellings the keyword admits and
// which of them reaches a key. What is left here are the two rules that speak
// about the values around it: the uniqueness of the three designations for one
// entity, and the value going out as it came in.
//
// Both are preprocessor-stage rules. The uniqueness one is
// Preprocessor::CheckDataKeyDesignationValue
// (src/preprocessor/preprocessor_protect_keynames.cpp), reached from the
// expression-shaped designation §34.5.12.1 writes and from the two §34.5.13.1
// and §34.5.14.1 write as a keyword standing alone with the value on the line
// beneath it; the output one is ProtectDataKeyownerDirective
// (src/preprocessor/protect_keywords.cpp), which the envelope writer calls.
//
// The three designations are spelled here as their own subclauses spell them,
// so a value reaching the rule reaches it the way a source text sends it and
// not through the one spelling that happens to be easiest to write.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity whose keys the designations below pick among.
constexpr std::string_view kOwner = "acme-semiconductor";

// A second entity. One value is unique for the entity it is written under, so
// the same characters under two entities are two designations rather than one
// repeated, and this is what that claim is made with.
constexpr std::string_view kOtherOwner = "globex-ip";

// The value written against two of the three designating names, which is what
// the rule forbids for one entity.
constexpr std::string_view kSharedValue = "one-designation";

// A second value, for the pair that designates two keys rather than one twice.
constexpr std::string_view kOtherValue = "another-designation";

// The design a region seals, for the output rule below.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

ProtectEncoding BlockEncoding() { return DefaultProtectEncoding(); }

// The directive §34.5.10.1 names the entity with.
std::string NamesKeyOwner(std::string_view owner) {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(owner).append("\"\n");
  return text;
}

// The directive §34.5.12.1 names one of that entity's keys with. This is the
// designation written against its keyword.
std::string NamesKeyName(std::string_view keyname) {
  std::string text = "`pragma protect data_keyname=\"";
  text.append(keyname).append("\"\n");
  return text;
}

// The two lines §34.5.13.1 spells a public key over: the keyword standing
// alone, and the encoded value on the line beneath it.
std::string DesignatesPublicKey(std::string_view value) {
  std::string text = "`pragma protect data_public_key\n";
  text.append(EncodeProtectBlock(value, BlockEncoding())).append("\n");
  return text;
}

// The two lines §34.5.14.1 spells a decryption key over, in the same shape.
std::string DesignatesDecryptKey(std::string_view value) {
  std::string text = "`pragma protect data_decrypt_key\n";
  text.append(EncodeProtectBlock(value, BlockEncoding())).append("\n");
  return text;
}

// A decryption envelope as another tool wrote it. The two designations spelled
// as a keyword standing alone are read only inside one, an announcement outside
// every envelope being text of the design rather than a value.
std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

// A reading of `src`, with the diagnostics it raised kept.
struct Read {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit Read(const std::string& src) {
    Preprocessor pp(mgr, diag, PreprocConfig{});
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  // Whether the reading reported anything carrying `message`. The cases that
  // expect nothing name the message they expect nothing of, so a run reporting
  // something else entirely does not read as the rule holding.
  bool Reported(std::string_view message) const {
    for (const auto& d : diag.Diagnostics()) {
      if (d.message.find(message) != std::string::npos) return true;
    }
    return false;
  }
};

// The message the uniqueness rule reports with.
constexpr std::string_view kTwoNamesOneValue =
    "writes one value against two of the names that designate a key of the "
    "data_keyowner in effect";

// §34.5.10.2: the values written against data_keyname, data_decrypt_key and
// data_public_key are unique for the entity named. The key name and the public
// key here carry one value under one entity, so that value would have to
// designate two of the entity's keys at once. §34.5.13.1 writes the public key
// as a keyword standing alone with its value beneath it, which is the spelling
// a rule reading only the value written against a keyword never sees.
TEST(ProtectDataKeyownerDescription, PublicKeyRepeatingTheKeyNameIsReported) {
  std::string described = NamesKeyOwner(kOwner);
  described += NamesKeyName(kSharedValue);
  described += DesignatesPublicKey(kSharedValue);
  Read run(ForeignEnvelope(described));
  // The report stands at the line the announced value is on, which is the line
  // the designation is read from, rather than at the keyword announcing it.
  EXPECT_TRUE(
      ReportedError(run.diag.Diagnostics(), kTwoNamesOneValue, 5, "34.5.10"));
}

// §34.5.10.2: the same of the third designating name. §34.5.14.1 spells the
// decryption key the way §34.5.13.1 spells the public key, so it reaches the
// rule by its own path and neither case stands for the other.
TEST(ProtectDataKeyownerDescription, DecryptKeyRepeatingTheKeyNameIsReported) {
  std::string described = NamesKeyOwner(kOwner);
  described += NamesKeyName(kSharedValue);
  described += DesignatesDecryptKey(kSharedValue);
  Read run(ForeignEnvelope(described));
  // The report stands at the line the announced value is on, which is the line
  // the designation is read from, rather than at the keyword announcing it.
  EXPECT_TRUE(
      ReportedError(run.diag.Diagnostics(), kTwoNamesOneValue, 5, "34.5.10"));
}

// §34.5.10.2: the values are unique for the entity specified, so two entities
// each designating a key by the same characters designate two keys. Reporting
// this would make the rule one about the characters rather than about the
// entity they are unique for.
TEST(ProtectDataKeyownerDescription,
     OneValueUnderTwoEntitiesIsTwoDesignations) {
  std::string described = NamesKeyOwner(kOwner);
  described += NamesKeyName(kSharedValue);
  described += NamesKeyOwner(kOtherOwner);
  described += DesignatesPublicKey(kSharedValue);
  Read run(ForeignEnvelope(described));
  EXPECT_FALSE(run.Reported(kTwoNamesOneValue));
}

// §34.5.10.2: two designating names carrying different values under one entity
// pick out two of that entity's keys, which is what the names are for. Without
// this the cases above would hold of an implementation reporting every second
// designation an entity writes.
TEST(ProtectDataKeyownerDescription, DistinctValuesUnderOneEntityAreLeftAlone) {
  std::string described = NamesKeyOwner(kOwner);
  described += NamesKeyName(kSharedValue);
  described += DesignatesPublicKey(kOtherValue);
  Read run(ForeignEnvelope(described));
  EXPECT_FALSE(run.Reported(kTwoNamesOneValue));
}

// §34.5.10.2: the data_keyowner is unchanged in the output file. §22.5.1 admits
// a bare identifier as a pragma_value, so an entity named with one is named
// with those characters; writing it back as a string would change the value the
// source wrote. No digital signature is in play here, which is the one case the
// subclause excepts.
TEST(ProtectDataKeyownerDescription,
     TheEntityGoesOutInTheSpellingItCameInWith) {
  std::string region = "`pragma protect begin\n";
  region += "`pragma protect data_keyowner=acme_semiconductor\n";
  region.append(kSealedDesign);
  region += "`pragma protect end\n";
  std::string envelope = EncryptEnvelopes(region, "one-key-of-the-authors-own");
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_NE(envelope.find("data_keyowner=acme_semiconductor"),
            std::string::npos)
      << envelope;
}

}  // namespace
