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

// Exercises the syntax of the `key_keyowner` protect pragma keyword
// (§34.5.23.1). The syntax block defines the keyword expression as
// `key_keyowner = <string>`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including its string argument.
struct ProtectKeyKeyownerSyntaxTest : ::testing::Test {
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

// The `key_keyowner = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectKeyKeyownerSyntaxTest, PragmaProtectKeyKeyownerConsumed) {
  auto result = Preprocess("`pragma protect key_keyowner = \"Acme Corp\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("Acme Corp"), std::string::npos);
}

// Only the key_keyowner directive line is removed; neighboring source text
// survives, confirming it is the key_keyowner keyword expression line that the
// pragma path consumes.
TEST_F(ProtectKeyKeyownerSyntaxTest,
       KeyKeyownerDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect key_keyowner = \"Acme Corp\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The two cases above observe the directive line going away, which any
// directive the pragma handler consumes does, and which a value written in a
// spelling §34.5.23.1 does not define brings about just as readily. What the
// subclause defines is the spelling: the keyword with a string written against
// it, and the string names the entity that provided the keys a region's own
// keys are under. The cases below read that entity back off the preprocessor,
// where ProtectKeywordScope::ValueOf in src/preprocessor/protect_keywords.cpp
// holds it, and then ask what naming it reaches.

// Two entities, each holding one key, and one name that picks a key out of
// either list. The name is the same in both lists, so what a reading reaches
// is decided by the entity and by nothing else: a case naming one of them
// fails where the entity was dropped rather than passing on the name alone.
constexpr std::string_view kFirstEntity = "meridian-trust";
constexpr std::string_view kSecondEntity = "cerulean-vault";
constexpr std::string_view kSharedKeyName = "wrapping-2027";
constexpr std::string_view kFirstEntityKey = "meridian-trust-wrapping-key";
constexpr std::string_view kSecondEntityKey = "cerulean-vault-wrapping-key";

// An entity whose name is spelled the way an identifier is, for the one case
// that writes the value bare. §22.11 reads a directive as tokens, and a hyphen
// is none of the characters an identifier holds: the two names above carry one,
// so writing either of them bare is rejected for the token the hyphen is rather
// than read as the value it was meant to be.
constexpr std::string_view kIdentifierEntity = "meridiantrust";

ProtectKeyList KeysOfBothEntities() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kFirstEntity, kSharedKeyName, kFirstEntityKey));
  keys.Add(KeyOf(kSecondEntity, kSharedKeyName, kSecondEntityKey));
  return keys;
}

// A directive writing `value` against the keyword, spelled as it stands here.
std::string NamesEntity(std::string_view value) {
  std::string directive = "`pragma protect key_keyowner=";
  directive.append(value).append("\n");
  return directive;
}

// The name §34.5.25 picks the key out of that entity's list by. It is written
// beside the entity wherever a case asks which key a reading reaches, since
// §34.5.27 has the two consulted together and neither reaches a key alone.
std::string NamesTheKey() {
  std::string directive = "`pragma protect key_keyname=\"";
  directive.append(kSharedKeyName).append("\"\n");
  return directive;
}

// A pragma_value written as the string §34.5.23.1 defines the expression with.
std::string InQuotes(std::string_view value) {
  std::string text = "\"";
  text.append(value).append("\"");
  return text;
}

// A reading of `src` with the preprocessor kept alive, so both what the text
// left in effect and what that reaches among a tool's keys can be asked of it.
struct ReadSource {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, PreprocConfig{}};

  explicit ReadSource(const std::string& src) {
    pp.Preprocess(mgr.AddFile("<test>", src));
    EXPECT_FALSE(diag.HasErrors()) << src;
  }

  // The entity in effect where the reading stopped.
  ProtectKeywordValue Entity() const {
    return pp.ProtectKeywords().ValueOf(kKeyKeyownerKeyword);
  }

  // The key §34.5.27 opens a region's key block with, reached through the
  // entity in effect and the name written against it.
  std::string_view KeyReached(const ProtectKeyList& keys) const {
    return ProtectKeyBlockKey(pp.ProtectKeywords(), keys);
  }
};

// §34.5.23.1: the expression is `key_keyowner = <string>`, and what stands in
// effect afterwards is what was inside the quotation marks, without them.
TEST(ProtectKeyKeyownerSyntax, TheStringAgainstTheKeywordNamesTheEntity) {
  EXPECT_EQ(ReadSource(NamesEntity(InQuotes(kFirstEntity))).Entity().value,
            kFirstEntity);
}

// §22.5.1 admits a bare identifier as a pragma_value, and one written thing is
// what this keyword is defined with.
TEST(ProtectKeyKeyownerSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(ReadSource(NamesEntity(kIdentifierEntity)).Entity().value,
            kIdentifierEntity);
}

// The <string> operand as §22.5.1 admits it rather than as an identifier could
// be spelled: an entity named with a space in it is one written thing, and the
// whole of it stands in effect rather than the word it opens with.
TEST(ProtectKeyKeyownerSyntax, TheWholeOfASpaceBearingStringStandsInEffect) {
  EXPECT_EQ(ReadSource(NamesEntity(InQuotes("Acme Corp"))).Entity().value,
            "Acme Corp");
}

// A text that named no entity is left with none. §34.5.23.2 puts on this value
// the constraints §34.5.10.2 states for the entity whose keys the data are
// under, and it settles no default drawn from that keyword: an entity named
// for the data says nothing about who holds the keys those data's keys travel
// under, so the place stays empty rather than being filled from it.
TEST(ProtectKeyKeyownerSyntax, TheDataEntityDoesNotFillThePlaceLeftEmpty) {
  ProtectKeywordValue entity =
      ReadSource("`pragma protect data_keyowner=\"meridian-trust\"\n").Entity();
  EXPECT_TRUE(entity.defaulted);
  EXPECT_TRUE(entity.value.empty());
}

// §34.5.23.1 defines the expression with a string, and §22.5.1 makes a
// parenthesized pragma_value a list of further expressions rather than one
// written thing, so a list names no entity and the one named earlier stands.
TEST(ProtectKeyKeyownerSyntax, AListLeavesTheEntityAlreadyNamed) {
  std::string src = NamesEntity(InQuotes(kFirstEntity));
  src += NamesEntity("(held_by=\"cerulean-vault\")");
  EXPECT_EQ(ReadSource(src).Entity().value, kFirstEntity);
}

// The same list where no entity was named before it, which leaves the keyword
// at its default -- what makes the case above about the list rather than about
// the value that happened to precede it.
TEST(ProtectKeyKeyownerSyntax, AListOnItsOwnNamesNoEntity) {
  EXPECT_TRUE(ReadSource(NamesEntity("(held_by=\"cerulean-vault\")"))
                  .Entity()
                  .defaulted);
}

// The negative that makes the spelling matter: §34.5.23.1 writes a string
// against the keyword, so the name standing alone is the expression written in
// a spelling this subclause does not define and it names nobody.
//
// What is asserted is the value and not whether a default put it there. #3271
// records that a keyword written standing alone is kept as having stated an
// empty value, so the two are not told apart here; naming nobody is what this
// subclause turns on either way.
TEST(ProtectKeyKeyownerSyntax, TheKeywordStandingAloneNamesNoEntity) {
  EXPECT_TRUE(
      ReadSource("`pragma protect key_keyowner\n").Entity().value.empty());
}

// The '=' written after the keyword with nothing following it. §34.5.23.1 has a
// string standing there, and an '=' with no value after it is no
// pragma_expression in any spelling, so §22.11 reports it.
TEST(ProtectKeyKeyownerSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect key_keyowner =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// §34.5.23.1 spells one name, and a name that merely opens with those
// characters is a different one. A text writing the longer one has written a
// keyword §34.4 does not tabulate, so nothing is put in effect for the one it
// resembles.
TEST(ProtectKeyKeyownerSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  EXPECT_TRUE(ReadSource("`pragma protect key_keyowners=\"meridian-trust\"\n")
                  .Entity()
                  .defaulted);
}

// What the string is for. §34.5.27 has a region's key block opened by the key
// its entity holds under the name written beside it, so the entity named is
// what decides which of two tools' keys a reading reaches. Both entities hold a
// key under this one name, so nothing but the entity separates the two.
TEST(ProtectKeyKeyownerSyntax, TheEntityNamedDecidesWhichKeyIsReached) {
  ProtectKeyList keys = KeysOfBothEntities();
  EXPECT_EQ(ReadSource(NamesEntity(InQuotes(kFirstEntity)) + NamesTheKey())
                .KeyReached(keys),
            kFirstEntityKey);
  EXPECT_EQ(ReadSource(NamesEntity(InQuotes(kSecondEntity)) + NamesTheKey())
                .KeyReached(keys),
            kSecondEntityKey);
}

// The list read back where it matters. An expression naming no entity leaves
// the one named before it standing, so the key that entity holds is still what
// the reading reaches -- where a list taken as the value would have sent it to
// an entity no tool has keys for.
TEST(ProtectKeyKeyownerSyntax, AListLeavesTheKeyTheEntityNamedReaches) {
  ProtectKeyList keys = KeysOfBothEntities();
  std::string src = NamesEntity(InQuotes(kFirstEntity));
  src += NamesTheKey();
  src += NamesEntity("(held_by=\"cerulean-vault\")");
  EXPECT_EQ(ReadSource(src).KeyReached(keys), kFirstEntityKey);
}

}  // namespace
