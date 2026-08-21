#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

// Exercises the syntax of the `key_public_key` protect pragma keyword
// (§34.5.26.1). The syntax block defines the keyword as the bare word
// `key_public_key` with no same-line argument (the encoded key value, if any,
// appears on a following line per the Description). Protect pragmas are
// processed at the preprocessor stage, where the generic `pragma` handler
// recognizes the keyword and consumes the directive line.
struct ProtectKeyPublicKeySyntaxTest : ::testing::Test {
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

// The bare `key_public_key` keyword is accepted and the directive line is
// stripped.
TEST_F(ProtectKeyPublicKeySyntaxTest, PragmaProtectKeyPublicKeyConsumed) {
  auto result = Preprocess("`pragma protect key_public_key\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the key_public_key directive line is removed; neighboring source text
// survives, confirming it is the key_public_key keyword line that the pragma
// path consumes.
TEST_F(ProtectKeyPublicKeySyntaxTest,
       KeyPublicKeyDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect key_public_key\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The keyword carries no same-line argument: only the single directive line is
// consumed, so the following line of source is left intact and passed through
// as ordinary text. (Any interpretation of that next line as an encoded key
// value belongs to the Description, not the Syntax, of this keyword.)
TEST_F(ProtectKeyPublicKeySyntaxTest,
       KeyPublicKeyConsumesOnlyDirectiveLineFollowingLineKept) {
  auto result = Preprocess("`pragma protect key_public_key\nDEADBEEFKEYDATA\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("DEADBEEFKEYDATA"), std::string::npos);
}

// The three cases above observe the directive line going away, which any
// directive the pragma handler consumes does. What §34.5.26.1 defines is the
// spelling: the keyword stands alone, with nothing written against it, and the
// encoded value of the public key is on the line beneath. So the question a
// case asks of this keyword is what became of that line -- whether it was taken
// as the designation or left standing as text of the design.

// The public key a text designates its region's key by, and what a tool holding
// that designation reaches through it. §34.5.26 makes the public key an
// alternative to the name §34.5.25 spells, so a tool reaches one key through
// either, and the key list holds this designation where a name would stand.
constexpr std::string_view kDesignatedKey = "acme-public-key-of-2027";
constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kKeyItReaches = "meridian-trust-wrapping-key";

// `key` written under the coding scheme a text that stated none is read in,
// which is what the line beneath the keyword carries. A line that cannot be
// read out of that scheme designates nothing at all.
std::string Encoded(std::string_view key) {
  return EncodeProtectBlock(key, DefaultProtectEncoding());
}

// The entity §34.5.23 names, written where a case asks what the designation
// reaches: §34.5.26 has the public key combined with it, and neither reaches a
// key alone.
std::string NamesTheEntity() {
  std::string text = "`pragma protect key_keyowner=\"";
  text.append(kEntity).append("\"\n");
  return text;
}

// A decryption envelope as some other tool wrote it, carrying `described`.
// §34.5.26 has an encrypting tool write this keyword into each protected block
// the designation was used for, so a line beneath it is read as key material
// only inside an envelope; outside every envelope the text below it is source
// like any other.
std::string EnvelopeCarrying(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text += "`pragma protect end_protected\n";
  return text;
}

// The keyword standing alone, with the designation on the line beneath it.
std::string AnnouncesTheKey() {
  std::string text = "`pragma protect key_public_key\n";
  text.append(Encoded(kDesignatedKey)).append("\n");
  return text;
}

// §34.5.26.1: the expression is the keyword and nothing else, and what it
// states is that the line beneath it carries the encoded value of the public
// key. That value is what stands in effect afterwards, read out of the coding
// scheme the text is under.
TEST(ProtectKeyPublicKeySyntax, TheKeywordSpeaksForTheLineBeneathIt) {
  EXPECT_EQ(ReadKeywordScope(EnvelopeCarrying(AnnouncesTheKey()))
                .ValueOf(kKeyPublicKeyKeyword)
                .value,
            kDesignatedKey);
}

// The other half of speaking for a line: the line spoken for is key material
// rather than text of the design, so it does not come back out. A case reading
// the value alone would hold of a reading that took the designation and put the
// characters it was written as into the design as well.
TEST(ProtectKeyPublicKeySyntax, TheLineTheKeywordSpokeForIsNotDesignText) {
  ReadKeywordScope run(EnvelopeCarrying(AnnouncesTheKey()));
  EXPECT_FALSE(Holds(run.text, Encoded(kDesignatedKey))) << run.text;
}

// The negative that makes the spelling matter: the same name with a
// pragma_value written against it is the expression written in a spelling
// §34.5.26.1 does not define, so it speaks for no line. What stands in effect
// is what was written against the keyword, and the line beneath stays text of
// the design.
TEST(ProtectKeyPublicKeySyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  std::string described = "`pragma protect key_public_key=\"stated-here\"\n";
  described.append(Encoded(kDesignatedKey)).append("\n");
  ReadKeywordScope run(EnvelopeCarrying(described));
  EXPECT_EQ(run.ValueOf(kKeyPublicKeyKeyword).value, "stated-here");
  EXPECT_TRUE(Holds(run.text, Encoded(kDesignatedKey))) << run.text;
}

// §22.5.1 gives a pragma_value a parenthesized spelling as well, and it is a
// value against the keyword just as the single one is. §34.5.26.1 writes
// nothing against the keyword at all, so this speaks for no line either.
TEST(ProtectKeyPublicKeySyntax, AListAgainstTheKeywordSpeaksForNoLine) {
  std::string described =
      "`pragma protect key_public_key=(held_by=\"meridian-trust\")\n";
  described.append(Encoded(kDesignatedKey)).append("\n");
  ReadKeywordScope run(EnvelopeCarrying(described));
  EXPECT_TRUE(Holds(run.text, Encoded(kDesignatedKey))) << run.text;
}

// §34.5.26.1 spells one name, and a name that merely opens with those
// characters is a different one. A text writing the longer one has written a
// keyword §34.4 does not tabulate, so the line beneath it is announced by
// nothing and stays text of the design.
TEST(ProtectKeyPublicKeySyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  std::string described = "`pragma protect key_public_key_of_theirs\n";
  described.append(Encoded(kDesignatedKey)).append("\n");
  ReadKeywordScope run(EnvelopeCarrying(described));
  EXPECT_TRUE(run.ValueOf(kKeyPublicKeyKeyword).defaulted);
  EXPECT_TRUE(Holds(run.text, Encoded(kDesignatedKey))) << run.text;
}

// §22.11 writes a directive's expressions as a comma-separated list, and an
// expression that is a keyword standing alone is one of the forms that list
// admits. The keyword speaks for the line beneath the directive it stands in,
// whatever else was written on that directive.
TEST(ProtectKeyPublicKeySyntax, TheKeywordStandsAloneAmongOtherExpressions) {
  std::string described =
      "`pragma protect key_keyowner=\"meridian-trust\", key_public_key\n";
  described.append(Encoded(kDesignatedKey)).append("\n");
  EXPECT_EQ(ReadKeywordScope(EnvelopeCarrying(described))
                .ValueOf(kKeyPublicKeyKeyword)
                .value,
            kDesignatedKey);
}

// The '=' written after the keyword with nothing following it. The spelling
// §34.5.26.1 defines has nothing after the keyword at all, and an '=' with no
// value after it is no pragma_expression in any spelling, so §22.11 reports it.
TEST(ProtectKeyPublicKeySyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect key_public_key =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// Where the announcement is read at all. §34.5.26 has an encrypting tool write
// this keyword into a protected block, so a line beneath it is key material
// only inside one. The same two lines outside every envelope announce nothing,
// and the line beneath is text of the design like any other.
//
// What is asserted about the designation is that there is none, rather than
// that a default stands where one would be. §34.4 records the keyword as
// written whether or not it announced anything, and #3271 records that a
// keyword standing alone is kept as having stated an empty value, so the two
// are not told apart here. Designating no key is what this case turns on.
TEST(ProtectKeyPublicKeySyntax, TheAnnouncementIsReadOnlyInsideAnEnvelope) {
  ReadKeywordScope run(AnnouncesTheKey());
  EXPECT_TRUE(run.ValueOf(kKeyPublicKeyKeyword).value.empty());
  EXPECT_TRUE(Holds(run.text, Encoded(kDesignatedKey))) << run.text;
}

// What the designation is for. §34.5.26 makes the public key an alternative to
// the name §34.5.25 spells, so a tool holding a key under this designation
// reaches it through the entity and the designation together.
TEST(ProtectKeyPublicKeySyntax, TheDesignationReachesTheKeyItNames) {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kDesignatedKey, kKeyItReaches));
  EXPECT_EQ(
      ReadKeywordScope(EnvelopeCarrying(NamesTheEntity() + AnnouncesTheKey()))
          .KeyBlockKeyReached(keys),
      kKeyItReaches);
}

}  // namespace
