#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

// Exercises the syntax of the `digest_keyname` protect pragma keyword
// (§34.5.18.1). The syntax block defines the keyword expression as
// `digest_keyname = <string>`. Protect pragmas are processed at the
// preprocessor stage, where the generic `pragma` handler recognizes the keyword
// expression and consumes the directive line, including its string argument.
struct ProtectDigestKeynameSyntaxTest : ::testing::Test {
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

// The `digest_keyname = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectDigestKeynameSyntaxTest, PragmaProtectDigestKeynameConsumed) {
  auto result = Preprocess("`pragma protect digest_keyname = \"key1\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("key1"), std::string::npos);
}

// Only the digest_keyname directive line is removed; neighboring source text
// survives, confirming it is the digest_keyname keyword expression line that
// the pragma path consumes.
TEST_F(ProtectDigestKeynameSyntaxTest,
       DigestKeynameDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect digest_keyname = \"key1\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// Edge case for the `<string>` operand: a multi-word, space-bearing value is
// consumed in full along with the directive, confirming the whole keyword
// expression (not just a leading token) is taken by the pragma path.
TEST_F(ProtectDigestKeynameSyntaxTest,
       DigestKeynameStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect digest_keyname = \"project alpha key\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("project alpha key"), std::string::npos);
}

// The cases above observe the directive line going away, which any directive
// the pragma handler consumes does. What §34.5.18.1 defines is the value the
// expression states, so the cases below read that value back off the
// preprocessor once the whole text has passed through it.

// What the keyword scope holds for digest_keyname after reading `src`, with the
// reading required to have gone through without a report so that a case reading
// the value is not reading one a rejected directive left behind.
ProtectKeywordValue DigestKeynameAfter(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << src;
  return pp.ProtectKeywords().ValueOf(kDigestKeynameKeyword);
}

// One protect pragma directive writing `value` against the keyword exactly as
// given, so what stands against the '=' is what a case is about.
std::string NamesDigestKey(std::string_view value) {
  std::string directive = "`pragma protect digest_keyname=";
  directive.append(value).append("\n");
  return directive;
}

// §34.5.18.1: the expression is `digest_keyname = <string>`, and the string
// names the key the digest is under. What stands in effect afterwards is what
// was inside the quotation marks, without them, and it is stated rather than
// defaulted.
TEST(ProtectDigestKeynameSyntax, TheStringAgainstTheKeywordNamesTheKey) {
  EXPECT_EQ(DigestKeynameAfter(NamesDigestKey("\"sigil-7\"")).value, "sigil-7");
}

// The same reading, on whether the name was stated. §34.5.18.2 fills the place
// from elsewhere when nothing states it, so a case reading only the characters
// cannot tell a name this directive wrote from one it inherited.
TEST(ProtectDigestKeynameSyntax, TheStringAgainstTheKeywordIsNoDefault) {
  EXPECT_FALSE(DigestKeynameAfter(NamesDigestKey("\"sigil-7\"")).defaulted);
}

// §34.5.18.1: a string is one written thing however many words are inside it,
// so a key named with spaces is one value rather than several expressions.
TEST(ProtectDigestKeynameSyntax, ANameHoldingSpacesIsOneValue) {
  EXPECT_EQ(DigestKeynameAfter(NamesDigestKey("\"the winter sigil\"")).value,
            "the winter sigil");
}

// §22.5.1 admits a bare identifier as a pragma_value, and one written thing is
// what this keyword is defined with, so a key named without quotation marks is
// named.
TEST(ProtectDigestKeynameSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(DigestKeynameAfter(NamesDigestKey("sigil_7")).value, "sigil_7");
}

// §34.5.18.1 defines the expression with a string, and §22.5.1 makes a
// parenthesized pragma_value a list of further expressions rather than one
// written thing, so a list names no key. Naming none is not naming an empty
// one: the key the text named earlier still stands, an expression naming
// nothing having no standing to take it away.
TEST(ProtectDigestKeynameSyntax, AListLeavesTheNameAlreadyWrittenStanding) {
  std::string src = NamesDigestKey("\"sigil-7\"");
  src += NamesDigestKey("(held_by=\"acme\")");
  EXPECT_EQ(DigestKeynameAfter(src).value, "sigil-7");
}

// The same list where no key was named before it. It names none, so the keyword
// stands at its default -- which is what makes the case above about the list
// rather than about the value that happened to precede it.
TEST(ProtectDigestKeynameSyntax, AListOnItsOwnNamesNoKey) {
  EXPECT_TRUE(
      DigestKeynameAfter(NamesDigestKey("(held_by=\"acme\")")).defaulted);
}

// The '=' written with nothing after it. The spelling this keyword is defined
// in has a value against the '=', so a directive without one is no expression
// at all and §22.11 reports it.
TEST(ProtectDigestKeynameSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect digest_keyname =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

}  // namespace
