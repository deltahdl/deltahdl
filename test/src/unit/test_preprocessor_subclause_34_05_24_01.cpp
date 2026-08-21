#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

// Exercises the syntax of the `key_method` protect pragma keyword
// (§34.5.24.1). The syntax block defines the keyword expression as
// `key_method = <string>`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including its string argument.
struct ProtectKeyMethodSyntaxTest : ::testing::Test {
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

// The `key_method = <string>` keyword expression is accepted and the directive
// line is stripped, including its string value.
TEST_F(ProtectKeyMethodSyntaxTest, PragmaProtectKeyMethodConsumed) {
  auto result = Preprocess("`pragma protect key_method = \"rsa\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("rsa"), std::string::npos);
}

// Only the key_method directive line is removed; neighboring source text
// survives, confirming it is the key_method keyword expression line that the
// pragma path consumes.
TEST_F(ProtectKeyMethodSyntaxTest,
       KeyMethodDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect key_method = \"rsa\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The two cases above observe the directive line going away, which any
// directive the pragma handler consumes does, and which a value written in a
// spelling §34.5.24.1 does not define brings about just as readily. What the
// subclause defines is the spelling: the keyword with a string written against
// it, and the string names the algorithm a region's own keys are encrypted
// under. The cases below read that identifier back, both off a reading and off
// the envelope an encrypting run produces, the two halves of a tool asking the
// same line the same question.

// The identifier the cases state, which is the row Table 34-3 requires of every
// implementation. §34.5.24.2 gives this keyword no identifiers of its own and
// sends the reader to the ones written for the cipher the data are under, so
// what is tabulated there answers here.
constexpr std::string_view kStated = "des-cbc";

// A tabulated identifier holding no hyphen, for the one case that writes the
// value bare. §22.11 reads a directive as tokens and a hyphen is none of the
// characters an identifier holds, so the value above written bare would be
// rejected for the token the hyphen is rather than read as a value at all.
constexpr std::string_view kIdentifierStated = "rsa";

// The design a region seals, and the key an author hands the encrypting half.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";
constexpr std::string_view kAuthorsKey = "one-key-of-the-authors-own";

// A directive writing `value` against the keyword, spelled as it stands here.
std::string StatesMethod(std::string_view value) {
  std::string directive = "`pragma protect key_method=";
  directive.append(value).append("\n");
  return directive;
}

// A pragma_value written as the string §34.5.24.1 defines the expression with.
// The identifier in effect once `src` has been read.
ProtectKeywordValue MethodAfter(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << src;
  return ProtectKeyMethodInEffect(pp.ProtectKeywords());
}

// The envelope this tool writes for a region stating `described`, checked on
// the way out to be one that sealed its design.
std::string EnvelopeStating(const std::string& described) {
  std::string region = "`pragma protect begin\n";
  region.append(described).append(kSealedDesign);
  region.append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(region, kAuthorsKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  return envelope;
}

// §34.5.24.1: the expression is `key_method = <string>`, and what stands in
// effect afterwards is what was inside the quotation marks, without them.
TEST(ProtectKeyMethodSyntax, TheStringAgainstTheKeywordStatesTheAlgorithm) {
  EXPECT_EQ(MethodAfter(StatesMethod(InQuotes(kStated))).value, kStated);
}

// The same expression read as something the text stated rather than as a place
// left empty, which is what tells an identifier an author chose from one that
// was never written.
TEST(ProtectKeyMethodSyntax, AStatedAlgorithmIsNotADefaultedOne) {
  EXPECT_FALSE(MethodAfter(StatesMethod(InQuotes(kStated))).defaulted);
}

// §22.5.1 admits a bare identifier as a pragma_value, and one written thing is
// what this keyword is defined with.
TEST(ProtectKeyMethodSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(MethodAfter(StatesMethod(kIdentifierStated)).value,
            kIdentifierStated);
}

// The <string> operand as §22.5.1 admits it rather than as an identifier could
// be spelled: a value holding spaces is one written thing, and the whole of it
// stands in effect rather than the word it opens with.
TEST(ProtectKeyMethodSyntax, TheWholeOfASpaceBearingStringStandsInEffect) {
  EXPECT_EQ(MethodAfter(StatesMethod(InQuotes("des cbc variant"))).value,
            "des cbc variant");
}

// §34.5.24.2 settles no default for this keyword, and the cipher the data are
// under does not fill the place: §34.5.17.2 draws the digest's cipher from
// there and §34.5.24.2 draws nothing from anywhere, so a text that stated no
// algorithm for its own keys has stated none.
TEST(ProtectKeyMethodSyntax, TheDataCipherDoesNotFillThePlaceLeftEmpty) {
  ProtectKeywordValue method =
      MethodAfter("`pragma protect data_method=\"des-cbc\"\n");
  EXPECT_TRUE(method.defaulted);
  EXPECT_TRUE(method.value.empty());
}

// §34.5.24.1 defines the expression with a string, and §22.5.1 makes a
// parenthesized pragma_value a list of further expressions rather than one
// written thing, so a list states no algorithm and the one stated earlier
// stands.
TEST(ProtectKeyMethodSyntax, AListLeavesTheAlgorithmAlreadyStated) {
  std::string src = StatesMethod(InQuotes(kStated));
  src += StatesMethod("(padding=\"pss\")");
  EXPECT_EQ(MethodAfter(src).value, kStated);
}

// The same list where no algorithm was stated before it, which leaves the
// keyword with none -- what makes the case above about the list rather than
// about the value that happened to precede it.
TEST(ProtectKeyMethodSyntax, AListOnItsOwnStatesNoAlgorithm) {
  ProtectKeywordValue method = MethodAfter(StatesMethod("(padding=\"pss\")"));
  EXPECT_TRUE(method.defaulted);
  EXPECT_TRUE(method.value.empty());
}

// The negative that makes the spelling matter: §34.5.24.1 writes a string
// against the keyword, so the name standing alone is the expression written in
// a spelling this subclause does not define and it states no algorithm.
TEST(ProtectKeyMethodSyntax, TheKeywordStandingAloneStatesNoAlgorithm) {
  ProtectKeywordValue method = MethodAfter("`pragma protect key_method\n");
  EXPECT_TRUE(method.defaulted);
  EXPECT_TRUE(method.value.empty());
}

// The '=' written after the keyword with nothing following it. §34.5.24.1 has a
// string standing there, and an '=' with no value after it is no
// pragma_expression in any spelling, so §22.11 reports it.
TEST(ProtectKeyMethodSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect key_method =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// §34.5.24.1 spells one name, and a name that merely opens with those
// characters is a different one. A text writing the longer one has written a
// keyword §34.4 does not tabulate, so nothing is put in effect for the one it
// resembles.
TEST(ProtectKeyMethodSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  EXPECT_TRUE(
      MethodAfter("`pragma protect key_methods=\"des-cbc\"\n").defaulted);
}

// The other half of the tool asks the same line the same question. §34.5.24.2
// has the identifier unchanged in the output file, so a region stating one in
// the spelling §34.5.24.1 defines has it written onto the envelope as it stood.
TEST(ProtectKeyMethodSyntax, TheAlgorithmStatedReachesTheEnvelope) {
  EXPECT_TRUE(Holds(EnvelopeStating(StatesMethod(InQuotes(kStated))),
                    StatesMethod(InQuotes(kStated))));
}

// And the same list read by that half. An expression naming no algorithm has
// none to write out, so the envelope states none: an encrypting tool that took
// the list would put an expression §22.11 does not admit onto the envelope it
// produced, where a reader looking for the identifier that opens the key blocks
// would find that instead.
TEST(ProtectKeyMethodSyntax, AListReachesTheEnvelopeAsNothingAtAll) {
  EXPECT_FALSE(
      Holds(EnvelopeStating(StatesMethod("(padding=\"pss\")")), "key_method"));
}

}  // namespace
