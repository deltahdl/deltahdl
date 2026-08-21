#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "fixture_protect_encoding.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_block.h"

using namespace delta;

// Exercises the syntax of the `digest_block` protect pragma keyword
// (§34.5.22.1). The syntax block defines the keyword as the bare word
// `digest_block` with no arguments. Protect pragmas are processed at the
// preprocessor stage, where the generic `pragma` handler recognizes the
// keyword and consumes the directive line.
struct ProtectDigestBlockSyntaxTest : ::testing::Test {
 protected:
  std::string Preprocess(const std::string& src) {
    auto fid = mgr_.AddFile("<test>", src);
    Preprocessor pp(mgr_, diag_, config_);
    return pp.Preprocess(fid);
  }

  SourceManager mgr_;
  DiagEngine diag_{mgr_};
  PreprocConfig config_;
};

namespace {

// The bare `digest_block` keyword is accepted and the directive line is
// stripped.
TEST_F(ProtectDigestBlockSyntaxTest, PragmaProtectDigestBlockConsumed) {
  auto result = Preprocess("`pragma protect digest_block\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the digest_block directive line is removed; neighboring source text
// survives, confirming it is the digest_block keyword line that the pragma
// path consumes.
TEST_F(ProtectDigestBlockSyntaxTest,
       DigestBlockDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect digest_block\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The two cases above observe the directive line going away, which any
// directive the pragma handler consumes does. What §34.5.22.1 defines is the
// spelling, and this keyword is written twice over in one text: between a
// region's delimiters it asks for a digest, and in what an encrypting tool
// produces it announces that the digest stands on the line beneath it.
//
// The spelling decides the second and not the first. §34.5.22.2 makes a
// digest_block "found in an input file" the request, which is a rule about the
// keyword being written rather than about what it carries -- the reading
// §34.5.15.2 gets for the data block, and the one NamesKeyword in
// src/preprocessor/protect_pragma_line.h is for. What the keyword announces is
// read against the spelling instead, by AnnouncesDigestBlock in
// src/preprocessor/preprocessor_protect_keys.cpp, because the line beneath a
// keyword is spoken for only by a keyword with nothing written on its own line.

// The region a case seals asks for its digest between the delimiters rather
// than ahead of them. A request written outside every region is copied into
// what the tool produces, so the envelope would carry two directives of this
// name and a case rewriting "the" one would be picking between them. Written
// inside, the request travels into the block along with the design, and the
// only directive of this name left standing is the one the tool wrote.

// The envelope this tool writes for a region asking for a digest, with the
// announcement the tool made spelled `announced` instead. `announced` is one
// line, so every line of the envelope keeps the number it had.
std::string EnvelopeAnnouncing(std::string_view announced) {
  std::string envelope = EnvelopeAround(kDigestBlockLine);
  size_t at = envelope.find(kDigestBlockLine);
  EXPECT_NE(at, std::string::npos) << envelope;
  std::string rewritten = envelope;
  rewritten.replace(at, kDigestBlockLine.size(), announced);
  return rewritten;
}

// A reading of `src` by a tool holding the key the envelope was sealed under,
// with the preprocessor kept alive so the digest check it made can be read off.
//
// What §34.5.22.1's spelling settles is not output text but whether a check
// happened at all, so the reading is asked afterwards rather than searched.
struct ReadEnvelope {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, HoldingTheKey()};
  std::string text;

  explicit ReadEnvelope(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectDigestCheck DigestCheck() const { return pp.LastDigestBlockCheck(); }
};

// §34.5.22.1: the expression is the keyword and nothing else, and what it
// states is that the digest stands on the line beneath it. A reading that took
// that line as the digest checked it against the block above; one that did not
// reach a digest at all reports having checked nothing.
TEST(ProtectDigestBlockSyntax, TheKeywordSpeaksForTheLineBeneathIt) {
  ReadEnvelope run(EnvelopeAround(kDigestBlockLine));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The negative that makes the spelling matter: the same name with a
// pragma_value written against it is the expression written in a spelling
// §34.5.22.1 does not define, so it speaks for no line and the digest beneath
// it is checked against nothing.
TEST(ProtectDigestBlockSyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  ReadEnvelope run(EnvelopeAnnouncing(
      "`pragma protect digest_block=\"a-value-of-its-own\"\n"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kNotChecked);
}

// §22.5.1 gives a pragma_value a parenthesized spelling as well, and it is a
// value against the keyword just as the single one is. §34.5.22.1 writes
// nothing against the keyword at all, so this announces no line either.
TEST(ProtectDigestBlockSyntax, AListAgainstTheKeywordSpeaksForNoLine) {
  ReadEnvelope run(
      EnvelopeAnnouncing("`pragma protect digest_block=(bytes=\"20\")\n"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kNotChecked);
}

// §34.5.22.1 spells one name, and a name that merely opens with those
// characters is a different one. A text writing the longer one has written a
// keyword §34.4 does not tabulate, so the line beneath it is announced by
// nothing.
TEST(ProtectDigestBlockSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  ReadEnvelope run(
      EnvelopeAnnouncing("`pragma protect digest_block_of_theirs\n"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kNotChecked);
}

// §22.11 writes a directive's expressions as a comma-separated list, and an
// expression that is a keyword standing alone is one of the forms that list
// admits. The keyword speaks for the line beneath the directive it stands in,
// whatever else was written on that directive. §34.4 leaves the expression
// written beside it to nothing this reading acts on, so what the case varies is
// the company the keyword keeps.
//
// §34.5.30.2 is the one rule that acts on that company, and it does not reach
// here: it has a comment output in cleartext ahead of the data block of the
// begin-end it was found in, and this directive is written into an envelope the
// tool has already produced rather than into a region awaiting encryption.
TEST(ProtectDigestBlockSyntax, TheKeywordStandsAloneAmongOtherExpressions) {
  ReadEnvelope run(EnvelopeAnnouncing(
      "`pragma protect comment=\"stands beside it\", digest_block\n"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The '=' written after the keyword with nothing following it. The spelling
// §34.5.22.1 defines has nothing after the keyword at all, and an '=' with no
// value after it is no pragma_expression in any spelling, so §22.11 reports it.
TEST(ProtectDigestBlockSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect digest_block =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// The other half of what this keyword does. A region writing it in the spelling
// §34.5.22.1 defines is asking for a digest, and the envelope carries one: the
// request written inside the region is sealed away with the design, so the
// directive of this name standing in what came back is the tool's own.
TEST(ProtectDigestBlockSyntax, TheKeywordStandingAloneAsksForADigest) {
  EXPECT_TRUE(Holds(EnvelopeAround(kDigestBlockLine), kDigestBlockLine));
}

// A region that asked for none gets none, without which the case above would
// hold of a tool that wrote a digest into every envelope it produced.
TEST(ProtectDigestBlockSyntax, ARegionAskingForNoDigestGetsNone) {
  EXPECT_FALSE(Holds(EnvelopeAround(""), kDigestBlockLine));
}

// Where the spelling stops. §34.5.22.2 makes the request out of a digest_block
// "found in an input file", which is the wording §34.5.15.2 uses for the data
// block and is a rule about the keyword being written rather than about what it
// carries. So the value that leaves the keyword announcing no line still leaves
// it asking for a digest, and the envelope carries one.
TEST(ProtectDigestBlockSyntax,
     TheSpellingDecidesWhatIsAnnouncedNotWhatIsAsked) {
  std::string envelope =
      EnvelopeAround("`pragma protect digest_block=\"a-value-of-its-own\"\n");
  EXPECT_TRUE(Holds(envelope, kDigestBlockLine)) << envelope;
}

}  // namespace
