// §34.5.15.2 data_block, Description, on the two sides that carry the block.
//
// The subclause states three things. The first is a condition on an encrypting
// tool's input -- a block found outside a previously generated envelope is an
// error, and inside one it is ignored -- and the file named for §34.5.15 covers
// that and says so. The other two are what this file is for.
//
//   ENCRYPTION OUTPUT: the tool takes each begin-end block, encrypts its
//   contents, and then encodes the block as the encoding pragma expression
//   specifies. The resultant text is what it outputs.
//
//   DECRYPTION INPUT: the block is first read in the encoded form. The encoding
//   is reversed, and then the block is internally decrypted.
//
// The two are one claim seen from each side: the coding scheme in effect is
// what the block is written in, and reversing that scheme is a step a reading
// takes before it decrypts anything. So a region is sealed under a scheme it
// names, the envelope declares that scheme beside the block, and a reading that
// reverses the declared scheme recovers the design while one handed a different
// declaration does not.
//
// §34.5.9 defines the encoding expression and which schemes an implementation
// provides; what is written here is what the block does with the one in effect.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The design a region seals, and the key it is sealed under.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";
constexpr std::string_view kRegionKey = "one-key-of-the-authors-own";

// The scheme the regions below name. §34.5.9 marks it one every implementation
// provides, and it is not the one this tool falls back on, so a block written
// in it was written in the scheme the region asked for.
constexpr std::string_view kNamedScheme = "base64";

// A region naming `scheme` for its block, with the design between the
// delimiters of §34.5.1 and §34.5.2.
std::string RegionEncodedIn(std::string_view scheme) {
  std::string text = "`pragma protect begin\n";
  text += "`pragma protect encoding=(enctype=\"";
  text.append(scheme).append("\")\n");
  text.append(kSealedDesign);
  text += "`pragma protect end\n";
  return text;
}

// The envelope this tool writes for that region.
std::string EnvelopeEncodedIn(std::string_view scheme) {
  std::string envelope =
      EncryptEnvelopes(RegionEncodedIn(scheme), std::string(kRegionKey));
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  return envelope;
}

// A reading of `src` by a tool holding the key the region was sealed under.
std::string ReadBack(const std::string& src, PreprocFixture& f) {
  PreprocConfig config;
  config.protect_key = std::string(kRegionKey);
  return Preprocess(src, f, config);
}

// §34.5.15.2, encryption output: the block is encoded as the encoding pragma
// expression specifies, so the envelope declares the scheme the region named
// and the block stands beside that declaration. An envelope declaring some
// other scheme would be one a reading could not reverse.
TEST(ProtectDataBlockDescription, TheEnvelopeDeclaresTheSchemeTheRegionNamed) {
  std::string envelope = EnvelopeEncodedIn(kNamedScheme);
  EXPECT_NE(envelope.find("enctype=\"base64\""), std::string::npos) << envelope;
  EXPECT_NE(envelope.find("`pragma protect data_block"), std::string::npos)
      << envelope;
}

// §34.5.15.2, decryption input: the block is read in the encoded form, the
// encoding is reversed, and then the block is decrypted. Reading the envelope
// as it stands does all three and the design comes back.
TEST(ProtectDataBlockDescription, ReversingTheDeclaredSchemeOpensTheBlock) {
  PreprocFixture f;
  std::string read = ReadBack(EnvelopeEncodedIn(kNamedScheme), f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(read.find(kSealedDesign), std::string::npos) << read;
}

// The same block with the envelope declaring a different scheme, so the reading
// reverses an encoding the block was not written in. What that leaves is not
// the ciphertext, so the block does not open and the design stays sealed --
// which is what makes reversing the encoding a step rather than a formality.
TEST(ProtectDataBlockDescription, ReversingAnotherSchemeDoesNotOpenTheBlock) {
  std::string envelope = EnvelopeEncodedIn(kNamedScheme);
  const std::string kDeclared = "enctype=\"base64\"";
  auto at = envelope.find(kDeclared);
  ASSERT_NE(at, std::string::npos) << envelope;
  std::string altered = envelope;
  altered.replace(at, kDeclared.size(), "enctype=\"uuencode\"");

  PreprocFixture f;
  std::string read = ReadBack(altered, f);
  EXPECT_EQ(read.find(kSealedDesign), std::string::npos) << read;
}

}  // namespace
