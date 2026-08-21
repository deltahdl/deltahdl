#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

// Exercises the syntax of the `key_keyname` protect pragma keyword
// (§34.5.25.1). The syntax block defines the keyword expression as
// `key_keyname = <string>`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including its string argument.
struct ProtectKeyKeynameSyntaxTest : ::testing::Test {
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

// The `key_keyname = <string>` keyword expression is accepted and the directive
// line is stripped, including its string value.
TEST_F(ProtectKeyKeynameSyntaxTest, PragmaProtectKeyKeynameConsumed) {
  auto result = Preprocess("`pragma protect key_keyname = \"acme-key\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("acme-key"), std::string::npos);
}

// Only the key_keyname directive line is removed; neighboring source text
// survives, confirming it is the key_keyname keyword expression line that the
// pragma path consumes.
TEST_F(ProtectKeyKeynameSyntaxTest,
       KeyKeynameDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect key_keyname = \"acme-key\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The <string> argument of the keyword expression may carry embedded
// whitespace; the entire quoted value is consumed along with the directive
// line, exercising the <string> portion of `key_keyname = <string>`.
TEST_F(ProtectKeyKeynameSyntaxTest,
       KeyKeynameStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect key_keyname = \"acme rsa key 1\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("acme rsa key 1"), std::string::npos);
}

// The three cases above observe the directive line going away, which any
// directive the pragma handler consumes does, and which a value written in a
// spelling §34.5.25.1 does not define brings about just as readily. What the
// subclause defines is the spelling: the keyword with a string written against
// it, and the string names the key a region's own keys are encrypted under. The
// cases below read that name back, and then ask what naming it reaches.

// One entity holding two keys, each under a name of its own. §34.5.25 has the
// name combined with the entity to reach a key, so holding the entity fixed and
// varying the name leaves the name as the only thing separating the key one
// reading reaches from the key the other does.
constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kFirstKeyName = "wrapping-2026";
constexpr std::string_view kSecondKeyName = "wrapping-2027";
constexpr std::string_view kFirstKey = "meridian-trust-key-of-2026";
constexpr std::string_view kSecondKey = "meridian-trust-key-of-2027";

// A key name spelled the way an identifier is, for the one case that writes the
// value bare. §22.11 reads a directive as tokens and a hyphen is none of the
// characters an identifier holds, so the names above written bare would be
// rejected for the token the hyphen is rather than read as a value at all.
constexpr std::string_view kIdentifierKeyName = "wrapping2026";

ProtectKeyList KeysOfOneEntity() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kFirstKeyName, kFirstKey));
  keys.Add(KeyOf(kEntity, kSecondKeyName, kSecondKey));
  return keys;
}

// A directive writing `value` against the keyword, spelled as it stands here.
std::string NamesKey(std::string_view value) {
  std::string directive = "`pragma protect key_keyname=";
  directive.append(value).append("\n");
  return directive;
}

// The entity §34.5.23 names, written beside the name wherever a case asks which
// key a reading reaches: §34.5.25 has the two combined, and neither reaches a
// key alone.
std::string NamesTheEntity() {
  std::string directive = "`pragma protect key_keyowner=\"";
  directive.append(kEntity).append("\"\n");
  return directive;
}

// A pragma_value written as the string §34.5.25.1 defines the expression with.
std::string InQuotes(std::string_view value) {
  std::string text = "\"";
  text.append(value).append("\"");
  return text;
}

// A reading of `src` with the preprocessor kept alive, so both what the text
// left in effect and what that reaches among a tool's keys can be asked of it.
//
// No keys are configured. §34.5.25 has a name that reaches none of the keys an
// entity holds reported, and Preprocessor::CheckKeyKeyname asks that only where
// the tool knows the entity at all, so a reading supplied with no keys is one
// where the cases below vary the spelling and nothing else.
struct ReadSource {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, PreprocConfig{}};

  explicit ReadSource(const std::string& src) {
    pp.Preprocess(mgr.AddFile("<test>", src));
    EXPECT_FALSE(diag.HasErrors()) << src;
  }

  // The name in effect where the reading stopped.
  ProtectKeywordValue Name() const {
    return pp.ProtectKeywords().ValueOf(kKeyKeynameKeyword);
  }

  // The key §34.5.27 opens a region's key block with, reached through the name
  // in effect and the entity written beside it.
  std::string_view KeyReached(const ProtectKeyList& keys) const {
    return ProtectKeyBlockKey(pp.ProtectKeywords(), keys);
  }
};

// §34.5.25.1: the expression is `key_keyname = <string>`, and what stands in
// effect afterwards is what was inside the quotation marks, without them.
TEST(ProtectKeyKeynameSyntax, TheStringAgainstTheKeywordNamesTheKey) {
  EXPECT_EQ(ReadSource(NamesKey(InQuotes(kFirstKeyName))).Name().value,
            kFirstKeyName);
}

// §22.5.1 admits a bare identifier as a pragma_value, and one written thing is
// what this keyword is defined with.
TEST(ProtectKeyKeynameSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(ReadSource(NamesKey(kIdentifierKeyName)).Name().value,
            kIdentifierKeyName);
}

// The <string> operand as §22.5.1 admits it rather than as an identifier could
// be spelled: a key named with spaces in it is one written thing, and the whole
// of it stands in effect rather than the word it opens with.
TEST(ProtectKeyKeynameSyntax, TheWholeOfASpaceBearingStringStandsInEffect) {
  EXPECT_EQ(ReadSource(NamesKey(InQuotes("acme rsa key 1"))).Name().value,
            "acme rsa key 1");
}

// §34.5.25.1 defines the expression with a string, and §22.5.1 makes a
// parenthesized pragma_value a list of further expressions rather than one
// written thing, so a list names no key and the one named earlier stands.
TEST(ProtectKeyKeynameSyntax, AListLeavesTheKeyAlreadyNamed) {
  std::string src = NamesKey(InQuotes(kFirstKeyName));
  src += NamesKey("(held_by=\"meridian-trust\")");
  EXPECT_EQ(ReadSource(src).Name().value, kFirstKeyName);
}

// The same list where no key was named before it, which leaves the keyword at
// its default -- what makes the case above about the list rather than about the
// value that happened to precede it.
TEST(ProtectKeyKeynameSyntax, AListOnItsOwnNamesNoKey) {
  EXPECT_TRUE(
      ReadSource(NamesKey("(held_by=\"meridian-trust\")")).Name().defaulted);
}

// The negative that makes the spelling matter: §34.5.25.1 writes a string
// against the keyword, so the name standing alone is the expression written in
// a spelling this subclause does not define and it names no key.
//
// What is asserted is the value and not whether a default put it there. #3271
// records that a keyword written standing alone is kept as having stated an
// empty value, so the two are not told apart here; naming no key is what this
// subclause turns on either way.
TEST(ProtectKeyKeynameSyntax, TheKeywordStandingAloneNamesNoKey) {
  EXPECT_TRUE(ReadSource("`pragma protect key_keyname\n").Name().value.empty());
}

// The '=' written after the keyword with nothing following it. §34.5.25.1 has a
// string standing there, and an '=' with no value after it is no
// pragma_expression in any spelling, so §22.11 reports it.
TEST(ProtectKeyKeynameSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect key_keyname =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// §34.5.25.1 spells one name, and a name that merely opens with those
// characters is a different one. A text writing the longer one has written a
// keyword §34.4 does not tabulate, so nothing is put in effect for the one it
// resembles.
TEST(ProtectKeyKeynameSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  EXPECT_TRUE(ReadSource("`pragma protect key_keynames=\"wrapping-2026\"\n")
                  .Name()
                  .defaulted);
}

// What the string is for. §34.5.27 has a region's key block opened by the key
// the named entity holds under the name written beside it, so with one entity
// holding two keys the name is what decides which of them a reading reaches.
TEST(ProtectKeyKeynameSyntax, TheNameDecidesWhichKeyIsReached) {
  ProtectKeyList keys = KeysOfOneEntity();
  EXPECT_EQ(ReadSource(NamesTheEntity() + NamesKey(InQuotes(kFirstKeyName)))
                .KeyReached(keys),
            kFirstKey);
  EXPECT_EQ(ReadSource(NamesTheEntity() + NamesKey(InQuotes(kSecondKeyName)))
                .KeyReached(keys),
            kSecondKey);
}

// The list read back where it matters. An expression naming no key leaves the
// one named before it standing, so the key that name reaches is still what the
// reading arrives at -- where a list taken as the value would have sent it to a
// name the entity holds nothing under.
TEST(ProtectKeyKeynameSyntax, AListLeavesTheKeyTheNameReaches) {
  ProtectKeyList keys = KeysOfOneEntity();
  std::string src = NamesTheEntity();
  src += NamesKey(InQuotes(kFirstKeyName));
  src += NamesKey("(held_by=\"meridian-trust\")");
  EXPECT_EQ(ReadSource(src).KeyReached(keys), kFirstKey);
}

}  // namespace
