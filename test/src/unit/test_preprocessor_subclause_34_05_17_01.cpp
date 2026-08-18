#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

// Exercises the syntax of the `digest_key_method` protect pragma keyword
// (§34.5.17.1). The syntax block defines the keyword expression as
// `digest_key_method = <string>`. Protect pragmas are processed at the
// preprocessor stage, where the generic `pragma` handler recognizes the keyword
// expression and consumes the directive line, including its string argument.
struct ProtectDigestKeyMethodSyntaxTest : ::testing::Test {
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

// The `digest_key_method = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectDigestKeyMethodSyntaxTest, PragmaProtectDigestKeyMethodConsumed) {
  auto result = Preprocess("`pragma protect digest_key_method = \"sha256\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("sha256"), std::string::npos);
}

// Only the digest_key_method directive line is removed; neighboring source text
// survives, confirming it is the digest_key_method keyword expression line that
// the pragma path consumes.
TEST_F(ProtectDigestKeyMethodSyntaxTest,
       DigestKeyMethodDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect digest_key_method = \"sha256\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// Edge case for the `<string>` operand: a multi-word, space-bearing value is
// consumed in full along with the directive, confirming the whole keyword
// expression (not just a leading token) is taken by the pragma path.
TEST_F(ProtectDigestKeyMethodSyntaxTest,
       DigestKeyMethodStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect digest_key_method = \"rsa pss sha512\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("rsa pss sha512"), std::string::npos);
}

// The cases above observe the directive line going away, which any directive
// the pragma handler consumes does. What §34.5.17.1 defines is the value the
// expression states, so the cases below read that value back off the
// preprocessor.

// What the keyword scope holds for the keyword after reading `src`.
ProtectKeywordValue MethodAfter(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << src;
  return pp.ProtectKeywords().ValueOf(kDigestKeyMethodKeyword);
}

std::string StatesKeyMethod(std::string_view value) {
  std::string directive = "`pragma protect digest_key_method=";
  directive.append(value).append("\n");
  return directive;
}

// §34.5.17.1: the expression is `digest_key_method = <string>`, and the string
// states the algorithm the digest's key is encrypted with. What stands in
// effect afterwards is what was inside the quotation marks, without them.
TEST(ProtectDigestKeyMethodSyntax,
     TheStringAgainstTheKeywordStatesTheAlgorithm) {
  EXPECT_EQ(MethodAfter(StatesKeyMethod("\"rsa\"")).value, "rsa");
}

// §22.5.1 admits a bare identifier as a pragma_value, and one written thing is
// what this keyword is defined with.
TEST(ProtectDigestKeyMethodSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(MethodAfter(StatesKeyMethod("rsa")).value, "rsa");
}

// §34.5.17.1 defines the expression with a string, and §22.5.1 makes a
// parenthesized pragma_value a list of further expressions rather than one
// written thing, so a list states no algorithm and the one stated earlier
// stands.
TEST(ProtectDigestKeyMethodSyntax, AListLeavesTheAlgorithmAlreadyStated) {
  std::string src = StatesKeyMethod("\"rsa\"");
  src += StatesKeyMethod("(padding=\"pss\")");
  EXPECT_EQ(MethodAfter(src).value, "rsa");
}

// The same list where no algorithm was stated before it, which leaves the
// keyword at its default -- what makes the case above about the list rather
// than about the value that happened to precede it.
TEST(ProtectDigestKeyMethodSyntax, AListOnItsOwnStatesNoAlgorithm) {
  EXPECT_TRUE(MethodAfter(StatesKeyMethod("(padding=\"pss\")")).defaulted);
}

}  // namespace
