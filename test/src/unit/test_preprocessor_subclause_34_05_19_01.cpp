#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

// Exercises the syntax of the `digest_public_key` protect pragma keyword
// (§34.5.19.1). The syntax block defines the keyword as the bare word
// `digest_public_key` with no same-line argument (the encoded key value, if
// any, appears on a following line per the Description). Protect pragmas are
// processed at the preprocessor stage, where the generic `pragma` handler
// recognizes the keyword and consumes the directive line.
struct ProtectDigestPublicKeySyntaxTest : ::testing::Test {
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

// The bare `digest_public_key` keyword is accepted and the directive line is
// stripped.
TEST_F(ProtectDigestPublicKeySyntaxTest, PragmaProtectDigestPublicKeyConsumed) {
  auto result = Preprocess("`pragma protect digest_public_key\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the digest_public_key directive line is removed; neighboring source text
// survives, confirming it is the digest_public_key keyword line that the pragma
// path consumes.
TEST_F(ProtectDigestPublicKeySyntaxTest,
       DigestPublicKeyDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect digest_public_key\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The keyword carries no same-line argument: only the single directive line is
// consumed, so the following line of source is left intact and passed through
// as ordinary text. (Any interpretation of that next line as an encoded key
// value belongs to the Description, not the Syntax, of this keyword.)
TEST_F(ProtectDigestPublicKeySyntaxTest,
       DigestPublicKeyConsumesOnlyDirectiveLineFollowingLineKept) {
  auto result =
      Preprocess("`pragma protect digest_public_key\nDEADBEEFKEYDATA\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("DEADBEEFKEYDATA"), std::string::npos);
}

// The three cases above observe the directive line going away, which any
// directive the pragma handler consumes does. What §34.5.19.1 defines is the
// spelling: the keyword stands alone, with nothing written against it, and the
// value it designates is on the line beneath. The cases below read that back
// off the preprocessor.

// The public key a text designates its digest's key by.
constexpr std::string_view kDesignatedKey = "veritas-rsa-public-key";

// A reading of `src` with the preprocessor kept alive afterwards.
struct ReadDigestPublicKey {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, PreprocConfig{}};
  std::string text;

  explicit ReadDigestPublicKey(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectKeywordValue Designated() const {
    return pp.ProtectKeywords().ValueOf(kDigestPublicKeyKeyword);
  }
};

// `key` written under the coding scheme a text that stated none is read in,
// which is what the line beneath the keyword carries.
std::string Encoded(std::string_view key) {
  return EncodeProtectBlock(key, DefaultProtectEncoding());
}

// A decryption envelope as some other tool wrote it, carrying `described`.
// §34.5.19 has an encrypting tool write this keyword into each protected block
// the designation was used for, so a line beneath it is read as key material
// only inside an envelope; outside every envelope the text below it is source
// like any other.
std::string EnvelopeCarrying(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text += "`pragma protect end_protected\n";
  return text;
}

// §34.5.19.1: the expression is the keyword and nothing else, and what it
// states is that the line beneath it carries the encoded value of the public
// key. That value is what stands in effect afterwards, read out of the coding
// scheme the text is under.
TEST(ProtectDigestPublicKeySyntax, TheKeywordSpeaksForTheLineBeneathIt) {
  std::string described = "`pragma protect digest_public_key\n";
  described += Encoded(kDesignatedKey) + "\n";
  ReadDigestPublicKey run(EnvelopeCarrying(described));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Designated().value, kDesignatedKey);
}

// The negative that makes the spelling matter: the same name written with a
// pragma_value against it is the expression written in a spelling §34.5.19.1
// does not define, so it says nothing about the line beneath it and that line
// stays text of the design.
TEST(ProtectDigestPublicKeySyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  std::string described = "`pragma protect digest_public_key=\"stated-here\"\n";
  described += Encoded(kDesignatedKey) + "\n";
  ReadDigestPublicKey run(EnvelopeCarrying(described));
  EXPECT_EQ(run.Designated().value, "stated-here");
}

// §22.11 writes a directive's expressions as a comma-separated list, and an
// expression that is a keyword standing alone is one of the forms that list
// admits. The keyword speaks for the line beneath the directive it stands in,
// whatever else was written on that directive.
TEST(ProtectDigestPublicKeySyntax, TheKeywordStandsAloneAmongOtherExpressions) {
  std::string described =
      "`pragma protect digest_keyowner=\"veritas\", digest_public_key\n";
  described += Encoded(kDesignatedKey) + "\n";
  ReadDigestPublicKey run(EnvelopeCarrying(described));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Designated().value, kDesignatedKey);
}

// The '=' written after the keyword with nothing following it. The spelling
// §34.5.19.1 defines has nothing after the keyword at all, and an '=' with no
// value after it is no pragma_expression in any spelling, so §22.11 reports it.
TEST(ProtectDigestPublicKeySyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect digest_public_key =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// §34.5.19.1 spells one name, and a name that merely opens with those
// characters is a different one. A text writing the longer one has written a
// keyword §34.4 does not tabulate, so nothing is put in effect for the one it
// resembles.
TEST(ProtectDigestPublicKeySyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  ReadDigestPublicKey run(
      "`pragma protect digest_public_key_of_theirs=\"k\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Designated().defaulted);
}

}  // namespace
