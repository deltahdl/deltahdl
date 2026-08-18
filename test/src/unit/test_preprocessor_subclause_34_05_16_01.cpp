#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

// Exercises the syntax of the `digest_keyowner` protect pragma keyword
// (§34.5.16.1). The syntax block defines the keyword expression as
// `digest_keyowner = <string>`. Protect pragmas are processed at the
// preprocessor stage, where the generic `pragma` handler recognizes the keyword
// expression and consumes the directive line, including its string argument.
struct ProtectDigestKeyownerSyntaxTest : ::testing::Test {
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

// The `digest_keyowner = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectDigestKeyownerSyntaxTest, PragmaProtectDigestKeyownerConsumed) {
  auto result = Preprocess("`pragma protect digest_keyowner = \"Acme Corp\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("Acme Corp"), std::string::npos);
}

// Only the digest_keyowner directive line is removed; neighboring source text
// survives, confirming it is the digest_keyowner keyword expression line that
// the pragma path consumes.
TEST_F(ProtectDigestKeyownerSyntaxTest,
       DigestKeyownerDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect digest_keyowner = \"Acme "
      "Corp\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The cases above observe the directive line going away, which any directive
// the pragma handler consumes does. What §34.5.16.1 defines is the value the
// expression states, so the cases below read that value back off the
// preprocessor, and one of them turns on what §34.5.16.2 does where no value
// was stated at all.

// What the keyword scope holds for `keyword` after reading `src`.
ProtectKeywordValue ScopeFor(const std::string& src, std::string_view keyword) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << src;
  return pp.ProtectKeywords().ValueOf(keyword);
}

std::string NamesDigestEntity(std::string_view value) {
  std::string directive = "`pragma protect digest_keyowner=";
  directive.append(value).append("\n");
  return directive;
}

// §34.5.16.1: the expression is `digest_keyowner = <string>`, and the string
// names the entity. What stands in effect afterwards is what was inside the
// quotation marks, without them.
TEST(ProtectDigestKeyownerSyntax, TheStringAgainstTheKeywordNamesTheEntity) {
  EXPECT_EQ(
      ScopeFor(NamesDigestEntity("\"Acme Corp\""), "digest_keyowner").value,
      "Acme Corp");
}

// §22.5.1 admits a bare identifier as a pragma_value, and one written thing is
// what this keyword is defined with, so an entity named without quotation marks
// is named.
TEST(ProtectDigestKeyownerSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(ScopeFor(NamesDigestEntity("acme_corp"), "digest_keyowner").value,
            "acme_corp");
}

// §34.5.16.1 defines the expression with a string, and §22.5.1 makes a
// parenthesized pragma_value a list of further expressions rather than one
// written thing, so a list names no entity. §34.5.16.2 then fills the place
// from the entity the data are under, which is what a keyword naming nobody
// leaves standing -- so a list is not a way of taking that default away.
TEST(ProtectDigestKeyownerSyntax, AListNamesNoEntityAndLeavesTheDefault) {
  std::string src = "`pragma protect data_keyowner=\"Acme Corp\"\n";
  src += NamesDigestEntity("(division=\"Widgets\")");
  EXPECT_TRUE(ScopeFor(src, "digest_keyowner").defaulted);
}

// The same list where the data name it would fall back to was never written
// either. It names nobody and there is nobody to fall back on, so the keyword
// stands at its default -- which is what makes the case above about the list
// rather than about the name beside it.
TEST(ProtectDigestKeyownerSyntax, AListOnItsOwnNamesNoEntity) {
  EXPECT_TRUE(
      ScopeFor(NamesDigestEntity("(division=\"Widgets\")"), "digest_keyowner")
          .defaulted);
}

}  // namespace
