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
// key it announces is on the line beneath.
//
// What the announcement leaves behind is spent before the envelope carrying it
// closes -- `Preprocessor::EndAccumulatedProtectPragmas` puts a key away with
// the block it was made for -- so the cases below observe the line being read
// at the moment it is read. §34.5.16 has the values designating one entity's
// digest key unique among themselves, and a key recovered from the line beneath
// this keyword is one of them, so a text writing that same value against the
// name of the digest's key has written one value against two of the three. The
// report stands on the line the value was read from, which is the line the
// keyword spoke for.

// The value a text writes in both places, so that one value stands against two
// of the names designating one entity's key. What it is does not matter; that
// the announced line carries it does.
constexpr std::string_view kSharedValue = "one-value-in-two-places";

// The report §34.5.16 draws from a value written against two of the three.
constexpr std::string_view kRepetition =
    "writes one value against two of the names that designate a key of the "
    "digest_keyowner in effect";

// `value` encoded as the coding scheme a text that stated none writes it.
std::string EncodedValue(std::string_view value) {
  return EncodeProtectBlock(value, DefaultProtectEncoding());
}

// The directive §34.5.18 names the digest's key with.
std::string NamesTheDigestKey(std::string_view value) {
  std::string text = "`pragma protect digest_keyname=\"";
  text.append(value).append("\"\n");
  return text;
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

// A reading of `src`, with the diagnostics it raised kept.
struct ReadEnvelope {
  SourceManager mgr;
  DiagEngine diag{mgr};

  explicit ReadEnvelope(const std::string& src) {
    Preprocessor pp(mgr, diag, PreprocConfig{});
    pp.Preprocess(mgr.AddFile("<test>", src));
  }
};

// §34.5.20.1: the expression is the keyword and nothing else, and what it
// states is that the line beneath it carries the encoded value of the key that
// opens the region's digest block. That line is read as the key's value, which
// is why writing the digest's key name there as well designates one key twice.
TEST(ProtectDigestDecryptKeySyntax, TheKeywordSpeaksForTheLineBeneathIt) {
  std::string src = EnvelopeCarrying(NamesTheDigestKey(kSharedValue) +
                                     "`pragma protect digest_decrypt_key\n" +
                                     EncodedValue(kSharedValue) + "\n");
  ReadEnvelope run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(), kRepetition,
                            LineHolding(src, EncodedValue(kSharedValue)),
                            "34.5.16"));
}

// The negative that makes the spelling matter: the same name written with a
// pragma_value against it is the expression written in a spelling §34.5.20.1
// does not define, so it speaks for no line and the value beneath it designates
// nothing. The value written against it is one nothing else in the text writes,
// so the only repetition available is the one the line below would have made.
TEST(ProtectDigestDecryptKeySyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  ReadEnvelope run(EnvelopeCarrying(
      NamesTheDigestKey(kSharedValue) +
      "`pragma protect digest_decrypt_key=\"a-value-of-its-own\"\n" +
      EncodedValue(kSharedValue) + "\n"));
  EXPECT_FALSE(run.diag.HasErrors());
}

// §22.11 writes a directive's expressions as a comma-separated list, and an
// expression that is a keyword standing alone is one of the forms that list
// admits. The keyword speaks for the line beneath the directive it stands in,
// whatever else was written on that directive.
TEST(ProtectDigestDecryptKeySyntax,
     TheKeywordStandsAloneAmongOtherExpressions) {
  std::string src = EnvelopeCarrying(
      "`pragma protect digest_keyname=\"one-value-in-two-places\", "
      "digest_decrypt_key\n" +
      EncodedValue(kSharedValue) + "\n");
  ReadEnvelope run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(), kRepetition,
                            LineHolding(src, EncodedValue(kSharedValue)),
                            "34.5.16"));
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
// nothing and the value on it designates nothing.
TEST(ProtectDigestDecryptKeySyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  ReadEnvelope run(
      EnvelopeCarrying(NamesTheDigestKey(kSharedValue) +
                       "`pragma protect digest_decrypt_key_of_theirs\n" +
                       EncodedValue(kSharedValue) + "\n"));
  EXPECT_FALSE(run.diag.HasErrors());
}

}  // namespace
