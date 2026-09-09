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
// Where the block stands is settled by the same subclause, in the sentence its
// expression is defined by: the expression indicates "that a data block begins
// on the next line in the file". So the resultant text carries the keyword
// alone on its directive, as §34.5.15.1 spells it, and the encoded characters
// on the line beneath. Issue #3272 records what this tool wrote before: the
// block stood against the keyword as its pragma_value, which put it on the
// directive rather than on the next line.
//
// §34.5.9 defines the encoding expression and which schemes an implementation
// provides; what is written here is what the block does with the one in effect.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "helpers_protect_block_lines.h"
#include "helpers_reported_error.h"
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

// The expression this tool writes to announce a block, as §34.5.15.1 spells it:
// the keyword standing alone on its own directive, and nothing after it on the
// line.
constexpr std::string_view kAnnouncingDirective =
    "`pragma protect data_block\n";

// §34.5.22's expression, which serves twice over. Written between a region's
// delimiters it asks for a digest, which is what makes the envelope carry one;
// written by the tool into the envelope it announces that digest on the line
// beneath it, immediately after the data block. So it is the `pragma directive
// the data block runs up against, and what it announces is checked against
// what that block recovered to.
constexpr std::string_view kDigestAnnouncingDirective =
    "`pragma protect digest_block\n";

// A region naming `scheme` for its block and writing `asks` between its
// delimiters, with the design after it.
std::string RegionEncodedIn(std::string_view scheme, std::string_view asks) {
  std::string text = "`pragma protect begin\n";
  text += "`pragma protect encoding=(enctype=\"";
  text.append(scheme).append("\")\n");
  text.append(asks);
  text.append(kSealedDesign);
  text += "`pragma protect end\n";
  return text;
}

// The envelope this tool writes for a region naming `scheme` and asking `asks`.
std::string EnvelopeOfRegion(std::string_view scheme, std::string_view asks) {
  std::string envelope =
      EncryptEnvelopes(RegionEncodedIn(scheme, asks), std::string(kRegionKey));
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  return envelope;
}

// The envelope for a region that asks for nothing beyond its scheme, which is
// what most cases here are about: no digest is requested, so the envelope
// carries the data block and no block after it.
std::string EnvelopeEncodedIn(std::string_view scheme) {
  return EnvelopeOfRegion(scheme, "");
}

// The characters standing on the line beneath the expression announcing the
// block, and empty where the envelope writes no such expression. §34.5.15.1
// spells the keyword alone, so the announcement is the whole directive, and
// §34.5.15.2 has the block begin on the line after it.
//
// The block is one line. EnvelopeBlockEncoding
// (src/preprocessor/protect_envelope_output.h) leaves the coding scheme no line
// length to break at, so the line the keyword announces is the whole of the
// block.
std::string BlockBeneathTheKeyword(std::string_view envelope) {
  size_t announced = envelope.find(kAnnouncingDirective);
  if (announced == std::string_view::npos) return {};
  std::string_view beneath =
      envelope.substr(announced + kAnnouncingDirective.size());
  return std::string(beneath.substr(0, beneath.find('\n')));
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
  EXPECT_NE(envelope.find(kAnnouncingDirective), std::string::npos) << envelope;
}

// §34.5.15.2, encryption output, on where the resultant text puts the block:
// the expression indicates that a block begins on the next line in the file, so
// the tool writes the keyword alone and the encoded characters beneath it.
//
// The characters are read back out of the envelope and opened under the key the
// region was sealed with, which is what says the line beneath the keyword is
// the block rather than a line that merely follows it. Asserting that no
// data_block carries a pragma_value is the other half: the spelling issue #3272
// records puts the same characters on the directive, and a text written that
// way would satisfy a search for the characters alone.
TEST(ProtectDataBlockDescription, TheBlockStandsOnTheLineBeneathTheKeyword) {
  std::string envelope = EnvelopeEncodedIn(kNamedScheme);
  ASSERT_EQ(envelope.find("`pragma protect data_block=\""), std::string::npos)
      << envelope;
  std::string cleartext;
  ASSERT_TRUE(DecryptProtectedRegion(BlockBeneathTheKeyword(envelope),
                                     kRegionKey, &cleartext, kNamedScheme))
      << envelope;
  // The region's own encoding directive travels into the block along with the
  // design, §34.5.9's expression being text the region enclosed, so what comes
  // back holds the design rather than being it.
  EXPECT_NE(cleartext.find(kSealedDesign), std::string::npos) << cleartext;
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

// §34.5.15.2, decryption input, on where the block ends: the subclause says the
// block begins on the next line in the file and says nothing about where it
// stops, so a block another tool wrote over several lines -- which is what
// §34.5.9.2's uuencode and quoted-printable produce by construction, and what
// any scheme produces under a stated line_length -- is a block this one has to
// read. The envelope here is the tool's own with its block broken across three
// lines by hand, so it differs from one that reads back in the breaks alone.
TEST(ProtectDataBlockDescription, ABlockStandingOnSeveralLinesIsReadWhole) {
  std::string envelope = EnvelopeEncodedIn(kNamedScheme);
  std::string broken =
      WithBlockBrokenIntoLines(envelope, kAnnouncingDirective, 3);
  ASSERT_NE(broken, envelope);
  // The first line no longer carries the block, which is what says the block
  // really was broken rather than left where it stood.
  ASSERT_LT(BlockBeneathTheKeyword(broken).size(),
            BlockBeneathTheKeyword(envelope).size());

  PreprocFixture f;
  std::string read = ReadBack(broken, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(read.find(kSealedDesign), std::string::npos) << read;
}

// The other half of "says nothing about where it ends": what ends it. A block
// runs to the next `pragma directive, none of §34.5.9.2's schemes spelling one,
// and that directive still takes effect. §34.5.22 puts the digest_block
// expression immediately after the block it vouches for, so a reading that
// swallowed that directive would check no digest -- and a digest altered by
// hand would then go unreported.
TEST(ProtectDataBlockDescription, TheDirectiveEndingABlockStillTakesEffect) {
  // §34.5.22.2 makes a digest_block written between the delimiters a request,
  // so this region is the one whose envelope carries a directive after the data
  // block for that block to run up against.
  std::string broken = WithBlockBrokenIntoLines(
      EnvelopeOfRegion(kNamedScheme, kDigestAnnouncingDirective),
      kAnnouncingDirective, 3);
  auto at = broken.find(kDigestAnnouncingDirective);
  ASSERT_NE(at, std::string::npos) << broken;
  // A character well inside the digest, which §34.5.22.2 puts on the line after
  // its own keyword. Counting past that directive's newline is what reaches the
  // digest rather than the expression announcing it.
  auto target = at + kDigestAnnouncingDirective.size() + 4;
  ASSERT_LT(target, broken.size());
  ASSERT_NE(broken[target], '\n') << broken;
  broken[target] = (broken[target] == 'A') ? 'B' : 'A';

  PreprocFixture f;
  ReadBack(broken, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma digest block disagrees with the block it follows, so one "
      "of the two was altered after encryption",
      LineHolding(broken, kDigestAnnouncingDirective) + 1, "34.5.22"));
}

// §34.5.15.2, decryption input: the block is read in the encoded form and that
// form is reversed, so the characters standing in the envelope are the block
// and not a copy of it kept elsewhere. Changing one of them changes what the
// reversal yields, and what that yields is no longer the ciphertext the key
// was made for, so the design stays sealed.
TEST(ProtectDataBlockDescription, TheEncodedCharactersAreWhatIsReversed) {
  std::string envelope = EnvelopeEncodedIn(kNamedScheme);
  auto at = envelope.find(kAnnouncingDirective);
  ASSERT_NE(at, std::string::npos) << envelope;
  // A character well inside the encoded run, which §34.5.15.2 puts on the line
  // after the directive. Counting past the directive's own newline is what
  // reaches the block rather than the expression announcing it, and the
  // character reached is asserted not to be the line's own end.
  auto target = at + kAnnouncingDirective.size() + 8;
  ASSERT_LT(target, envelope.size());
  ASSERT_NE(envelope[target], '\n') << envelope;
  std::string altered = envelope;
  altered[target] = (altered[target] == 'A') ? 'B' : 'A';

  PreprocFixture f;
  std::string read = ReadBack(altered, f);
  EXPECT_EQ(read.find(kSealedDesign), std::string::npos) << read;
}

}  // namespace
