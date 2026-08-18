// §34.5.11.2 data_method, Description.
//
// The subclause says four things about the keyword §34.5.11.1 spells.
//
//   Written in an encrypting tool's input, it states the encryption algorithm
//   that shall be used to encrypt the begin-end blocks that follow it, named by
//   an identifier commonly associated with a specific cipher.
//
//   Table 34-3 lists the identifiers the standard settles. des-cbc is required
//   of every implementation; the rest are optional, an implementation offering
//   one of those ciphers is required to offer it under the tabulated name, and
//   further identifiers and their ciphers are implementation-defined.
//
//   The data_method is unchanged in the output file, except where a digital
//   signature is used.
//
//   Read in a protected envelope, it states the algorithm the data_block is to
//   be decrypted with.
//
// The last of those is what this file is about, and it is the one an
// implementation offering a single cipher has to answer for. This tool provides
// one, states its own implementation-defined identifier for it in every
// envelope it writes, and cannot read a block written under any other. Reading
// such a block under the cipher it does provide would hand back whatever those
// bytes became rather than the design, so the identifier the envelope states is
// checked before the block is opened
// (Preprocessor::DecryptDataBlock,
// src/preprocessor/preprocessor_protect_keys.cpp).
//
// Table 34-3 itself is modelled in src/preprocessor/protect_key_method.h, which
// §34.5.24 shares, so the identifiers written below are the tabulated spellings
// rather than spellings invented here.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The design a region seals, and the key it is sealed under.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";
constexpr std::string_view kRegionKey = "one-key-of-the-authors-own";

// The report a block naming an algorithm this implementation does not provide
// draws.
constexpr std::string_view kNotProvided =
    "states an encryption algorithm this implementation does not provide";

// An envelope this tool wrote for a region holding the sealed design, which
// states the tool's own identifier and carries a block it can open.
std::string OurEnvelope() {
  std::string region = "`pragma protect begin\n";
  region.append(kSealedDesign);
  region += "`pragma protect end\n";
  std::string envelope = EncryptEnvelopes(region, std::string(kRegionKey));
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  return envelope;
}

// The same envelope with the algorithm it states replaced by `identifier`,
// which is how a block written under some other tool's cipher reaches a
// reading. Only the stated identifier changes; the block is left as it was, so
// what a case observes is the identifier deciding whether the block is opened.
std::string EnvelopeNaming(std::string_view identifier) {
  std::string envelope = OurEnvelope();
  std::string ours = "`pragma protect data_method=\"";
  ours.append(kDataMethod).append("\"");
  auto at = envelope.find(ours);
  EXPECT_NE(at, std::string::npos) << envelope;
  if (at == std::string::npos) return envelope;
  std::string theirs = "`pragma protect data_method=\"";
  theirs.append(identifier).append("\"");
  return envelope.replace(at, ours.size(), theirs);
}

// A reading of `src` by a tool holding the key the region was sealed under.
struct ReadBack {
  PreprocFixture f;
  std::string text;

  explicit ReadBack(const std::string& src) {
    PreprocConfig config;
    config.protect_key = std::string(kRegionKey);
    text = Preprocess(src, f, config);
  }

  bool Recovered() const {
    return text.find(kSealedDesign) != std::string::npos;
  }
};

// §34.5.11.2: the data_method states the algorithm the data block is decrypted
// with, and des-cbc is the identifier Table 34-3 requires of an implementation.
// This one does not provide it, so a block naming it is not opened and the
// reading says so rather than handing back what the tool's own cipher made of
// those bytes.
TEST(ProtectDataMethodDescription,
     ABlockNamingARequiredCipherWeLackIsReported) {
  ReadBack run(EnvelopeNaming("des-cbc"));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNotProvided,
                            LineHolding(run.text, "data_block"), "34.5.11.2"))
      << run.text;
  EXPECT_FALSE(run.Recovered()) << run.text;
}

// §34.5.11.2: the same of one of Table 34-3's optional identifiers. An
// implementation offering that cipher would have to offer it under this name,
// and this one does not offer it at all.
TEST(ProtectDataMethodDescription,
     ABlockNamingAnOptionalCipherWeLackIsReported) {
  ReadBack run(EnvelopeNaming("aes128-cbc"));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNotProvided,
                            LineHolding(run.text, "data_block"), "34.5.11.2"))
      << run.text;
  EXPECT_FALSE(run.Recovered()) << run.text;
}

// §34.5.11.2: further identifiers are implementation-defined, and one this tool
// does not know names a cipher it cannot read with all the same.
TEST(ProtectDataMethodDescription, ABlockNamingAnUnknownIdentifierIsReported) {
  ReadBack run(EnvelopeNaming("x-some-other-tools-cipher"));
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(), kNotProvided,
                            LineHolding(run.text, "data_block"), "34.5.11.2"))
      << run.text;
  EXPECT_FALSE(run.Recovered()) << run.text;
}

// §34.5.11.2: the identifier decides whether the block is read, so a block
// naming the algorithm this tool does provide is read. Without this the three
// cases above would hold of an implementation that refused every block.
TEST(ProtectDataMethodDescription, ABlockNamingTheCipherWeProvideIsRead) {
  ReadBack run(OurEnvelope());
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_TRUE(run.Recovered()) << run.text;
}

}  // namespace
