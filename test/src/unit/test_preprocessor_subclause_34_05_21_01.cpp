#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "fixture_program.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

// Exercises the syntax of the `digest_method` protect pragma keyword
// (§34.5.21.1). The syntax block defines the keyword expression as
// `digest_method = <string>`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including its string argument.
struct ProtectDigestMethodSyntaxTest : ::testing::Test {
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

// The `digest_method = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectDigestMethodSyntaxTest, PragmaProtectDigestMethodConsumed) {
  auto result = Preprocess("`pragma protect digest_method = \"sha256\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("sha256"), std::string::npos);
}

// Only the digest_method directive line is removed; neighboring source text
// survives, confirming it is the digest_method keyword expression line that the
// pragma path consumes.
TEST_F(ProtectDigestMethodSyntaxTest,
       DigestMethodDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect digest_method = \"sha256\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// Edge case for the `<string>` operand: a multi-word, space-bearing value is
// consumed in full along with the directive, confirming the whole keyword
// expression (not just a leading token) is taken by the pragma path.
TEST_F(ProtectDigestMethodSyntaxTest,
       DigestMethodStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect digest_method = \"sha 512 variant\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("sha 512 variant"), std::string::npos);
}

// The three cases above observe the directive line going away, which any
// directive the pragma handler consumes does. What §34.5.21.1 defines is the
// spelling: the keyword with a string written against it, and that string is
// the identifier naming the algorithm the digests written after it are computed
// under. The cases below read the identifier back off the preprocessor, where
// ProtectDigestMethodInEffect in src/preprocessor/protect_digest.cpp answers
// with what a directive wrote and, where none did, with the default.

// The identifier the cases below write. It is a row Table 34-4 marks required,
// so it names an algorithm every reader can recompute a digest under, and it is
// a different row from the one a text writing nothing is read under: a case
// stating this one fails where the reading fell through to the default instead
// of taking what was written.
constexpr std::string_view kStatedMethod = kMd5DigestMethod;
static_assert(kStatedMethod != kDefaultDigestMethod,
              "a case stating the identifier the default already supplies "
              "passes whether the expression was read or not");

// The identifier in effect once `src` has been read.
ProtectKeywordValue MethodAfter(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << src;
  return ProtectDigestMethodInEffect(pp.ProtectKeywords());
}

// A directive writing `value` against the keyword, spelled as it stands here.
std::string StatesMethod(std::string_view value) {
  std::string directive = "`pragma protect digest_method=";
  directive.append(value).append("\n");
  return directive;
}

// A pragma_value written as the string §34.5.21.1 defines the expression with.
// §34.5.21.1: the expression is `digest_method = <string>`, and what stands in
// effect afterwards is what was inside the quotation marks, without them.
TEST(ProtectDigestMethodSyntax, TheStringAgainstTheKeywordStatesTheAlgorithm) {
  EXPECT_EQ(MethodAfter(StatesMethod(InQuotes(kStatedMethod))).value,
            kStatedMethod);
}

// The same expression read as a directive rather than as a default: what a text
// wrote is held apart from what it was filled with, so a later reader can tell
// an identifier the author chose from one this implementation supplied.
TEST(ProtectDigestMethodSyntax, AStatedAlgorithmIsNotADefaultedOne) {
  EXPECT_FALSE(MethodAfter(StatesMethod(InQuotes(kStatedMethod))).defaulted);
}

// §22.5.1 admits a bare identifier as a pragma_value, and one written thing is
// what this keyword is defined with.
TEST(ProtectDigestMethodSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(MethodAfter(StatesMethod(kStatedMethod)).value, kStatedMethod);
}

// The <string> operand as §22.5.1 admits it rather than as an identifier could
// be spelled: a value holding spaces is one written thing, and the whole of it
// stands in effect rather than the word it opens with. §34.5.21.2 leaves an
// identifier outside Table 34-4 to the implementation, so a value like this is
// one the syntax admits and the description does not settle.
TEST(ProtectDigestMethodSyntax, TheWholeOfASpaceBearingStringStandsInEffect) {
  EXPECT_EQ(MethodAfter(StatesMethod(InQuotes("sha 512 variant"))).value,
            "sha 512 variant");
}

// §34.5.21.1 defines the expression with a string, and §22.5.1 makes a
// parenthesized pragma_value a list of further expressions rather than one
// written thing, so a list states no algorithm and the one stated earlier
// stands.
TEST(ProtectDigestMethodSyntax, AListLeavesTheAlgorithmAlreadyStated) {
  std::string src = StatesMethod(InQuotes(kStatedMethod));
  src += StatesMethod("(rounds=\"64\")");
  EXPECT_EQ(MethodAfter(src).value, kStatedMethod);
}

// The same list where no algorithm was stated before it, which leaves the
// keyword at its default -- what makes the case above about the list rather
// than about the value that happened to precede it.
TEST(ProtectDigestMethodSyntax, AListOnItsOwnStatesNoAlgorithm) {
  EXPECT_TRUE(MethodAfter(StatesMethod("(rounds=\"64\")")).defaulted);
}

// The negative that makes the spelling matter: §34.5.21.1 writes a string
// against the keyword, so the name standing alone is the expression written in
// a spelling this subclause does not define and it states no algorithm. What
// the reading is left under is the default, which is a different identifier
// from the one a text writing the defined spelling would have put there.
TEST(ProtectDigestMethodSyntax, TheKeywordStandingAloneStatesNoAlgorithm) {
  ProtectKeywordValue in_effect =
      MethodAfter("`pragma protect digest_method\n");
  EXPECT_TRUE(in_effect.defaulted);
  EXPECT_EQ(in_effect.value, kDefaultDigestMethod);
}

// The '=' written after the keyword with nothing following it. §34.5.21.1 has a
// string standing there, and an '=' with no value after it is no
// pragma_expression in any spelling, so §22.11 reports it.
TEST(ProtectDigestMethodSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect digest_method =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// §34.5.21.1 spells one name, and a name that merely opens with those
// characters is a different one. A text writing the longer one has written a
// keyword §34.4 does not tabulate, so nothing is put in effect for the one it
// resembles and the reading stays at the default.
TEST(ProtectDigestMethodSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  std::string src = "`pragma protect digest_method_of_theirs=";
  src.append(InQuotes(kStatedMethod)).append("\n");
  EXPECT_TRUE(MethodAfter(src).defaulted);
}

}  // namespace
