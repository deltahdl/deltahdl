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

using namespace delta;

// Exercises the syntax of the `digest_decrypt_key` protect pragma keyword
// (§34.5.20.1). The syntax block defines the keyword as the bare word
// `digest_decrypt_key` with no same-line argument (the encoded key value, if
// any, appears on a following line per the Description). Protect pragmas are
// processed at the preprocessor stage, where the generic `pragma` handler
// recognizes the keyword and consumes the directive line.
struct ProtectDigestDecryptKeySyntaxTest : ::testing::Test {
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

// The bare `digest_decrypt_key` keyword is accepted and the directive line is
// stripped.
TEST_F(ProtectDigestDecryptKeySyntaxTest,
       PragmaProtectDigestDecryptKeyConsumed) {
  auto result = Preprocess("`pragma protect digest_decrypt_key\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the digest_decrypt_key directive line is removed; neighboring source
// text survives, confirming it is the digest_decrypt_key keyword line that the
// pragma path consumes.
TEST_F(ProtectDigestDecryptKeySyntaxTest,
       DigestDecryptKeyDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect digest_decrypt_key\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The keyword carries no same-line argument: only the single directive line is
// consumed, so the following line of source is left intact and passed through
// as ordinary text. (Any interpretation of that next line as the encoded
// decrypt-key value belongs to the Description, not the Syntax, of this
// keyword.)
TEST_F(ProtectDigestDecryptKeySyntaxTest,
       DigestDecryptKeyConsumesOnlyDirectiveLineFollowingLineKept) {
  auto result =
      Preprocess("`pragma protect digest_decrypt_key\nDEADBEEFKEYDATA\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("DEADBEEFKEYDATA"), std::string::npos);
}

// The three cases above observe the directive line going away, which any
// directive the pragma handler consumes does. What §34.5.20.1 defines is the
// spelling: the keyword stands alone, with nothing written against it, and the
// key it announces is on the line beneath. The cases below read that back off
// the preprocessor.

// The key a protected block carries for the region's digests.
constexpr std::string_view kCarriedKey = "veritas-digest-session-key";

// A reading of `src` with the preprocessor kept alive afterwards.
struct ReadDigestDecryptKey {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, PreprocConfig{}};

  explicit ReadDigestDecryptKey(const std::string& src) {
    pp.Preprocess(mgr.AddFile("<test>", src));
  }

  std::string_view Carried() const { return pp.DigestDecryptKeyInEffect(); }
};

// `key` written under the coding scheme a text that stated none is read in,
// which is what the line beneath the keyword carries.
std::string EncodedKey(std::string_view key) {
  return EncodeProtectBlock(key, DefaultProtectEncoding());
}

// A decryption envelope as some other tool wrote it, carrying `described`.
// §34.5.20 has an encrypting tool write this keyword into the key block it made
// the key for, so a line beneath it is read as key material only inside an
// envelope; outside every envelope the text below it is source like any other.
std::string EnvelopeCarrying(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text += "`pragma protect end_protected\n";
  return text;
}

// §34.5.20.1: the expression is the keyword and nothing else, and what it
// states is that the line beneath it carries the encoded value of the key that
// opens the region's digest block. That key is what stands in effect
// afterwards, read out of the coding scheme the text is under.
TEST(ProtectDigestDecryptKeySyntax, TheKeywordSpeaksForTheLineBeneathIt) {
  std::string described = "`pragma protect digest_decrypt_key\n";
  described += EncodedKey(kCarriedKey) + "\n";
  ReadDigestDecryptKey run(EnvelopeCarrying(described));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Carried(), kCarriedKey);
}

// The negative that makes the spelling matter: the same name written with a
// pragma_value against it is the expression written in a spelling §34.5.20.1
// does not define, so it says nothing about the line beneath it and no key is
// recovered from that line.
TEST(ProtectDigestDecryptKeySyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  std::string described =
      "`pragma protect digest_decrypt_key=\"stated-here\"\n";
  described += EncodedKey(kCarriedKey) + "\n";
  ReadDigestDecryptKey run(EnvelopeCarrying(described));
  EXPECT_TRUE(run.Carried().empty());
}

// §22.11 writes a directive's expressions as a comma-separated list, and an
// expression that is a keyword standing alone is one of the forms that list
// admits. The keyword speaks for the line beneath the directive it stands in,
// whatever else was written on that directive.
TEST(ProtectDigestDecryptKeySyntax,
     TheKeywordStandsAloneAmongOtherExpressions) {
  std::string described =
      "`pragma protect digest_keyowner=\"veritas\", digest_decrypt_key\n";
  described += EncodedKey(kCarriedKey) + "\n";
  ReadDigestDecryptKey run(EnvelopeCarrying(described));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Carried(), kCarriedKey);
}

// The '=' written after the keyword with nothing following it. The spelling
// §34.5.20.1 defines has nothing after the keyword at all, and an '=' with no
// value after it is no pragma_expression in any spelling, so §22.11 reports it.
TEST(ProtectDigestDecryptKeySyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect digest_decrypt_key =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// §34.5.20.1 spells one name, and a name that merely opens with those
// characters is a different one. A text writing the longer one has written a
// keyword §34.4 does not tabulate, so the line beneath it is announced by
// nothing and no key comes out of it.
TEST(ProtectDigestDecryptKeySyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  std::string described = "`pragma protect digest_decrypt_key_of_theirs\n";
  described += EncodedKey(kCarriedKey) + "\n";
  ReadDigestDecryptKey run(EnvelopeCarrying(described));
  EXPECT_TRUE(run.Carried().empty());
}

}  // namespace
