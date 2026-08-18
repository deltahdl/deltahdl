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

// Exercises the syntax of the `data_keyname` protect pragma keyword
// (§34.5.12.1). The syntax block defines the keyword expression as
// `data_keyname = <string>`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including its string argument.
struct ProtectDataKeynameSyntaxTest : ::testing::Test {
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

// The `data_keyname = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectDataKeynameSyntaxTest, PragmaProtectDataKeynameConsumed) {
  auto result = Preprocess("`pragma protect data_keyname = \"primary-key\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("primary-key"), std::string::npos);
}

// Only the data_keyname directive line is removed; neighboring source text
// survives, confirming it is the data_keyname keyword expression line that the
// pragma path consumes.
TEST_F(ProtectDataKeynameSyntaxTest,
       DataKeynameDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect data_keyname = \"primary-key\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// Edge case: the `<string>` value of the keyword expression may contain
// internal whitespace; the directive line is still consumed in full, with no
// portion of the quoted value leaking into the output.
TEST_F(ProtectDataKeynameSyntaxTest,
       DataKeynameStringArgumentWithSpacesConsumed) {
  auto result = Preprocess("`pragma protect data_keyname = \"my key name\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("my key name"), std::string::npos);
}

// The cases above observe the directive line going away, which any directive
// the pragma handler consumes does. What §34.5.12.1 defines is the value the
// expression states, so the cases below read that value back off the
// preprocessor once the whole text has passed through it.

// A reading of `src` with the preprocessor kept alive afterwards.
struct ReadKeyname {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, PreprocConfig{}};
  std::string text;

  explicit ReadKeyname(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectKeywordValue Keyname() const {
    return pp.ProtectKeywords().ValueOf(kDataKeynameKeyword);
  }
};

// One protect pragma directive writing `value` against the keyword exactly as
// given, so what stands against the '=' is what a case is about.
std::string NamesKey(std::string_view value) {
  std::string directive = "`pragma protect data_keyname=";
  directive.append(value).append("\n");
  return directive;
}

// §34.5.12.1: the expression is `data_keyname = <string>`, and the string names
// the key. The value in effect afterwards is what stood in the quotation marks,
// without them, and it is stated rather than defaulted.
TEST(ProtectDataKeynameSyntax, TheStringAgainstTheKeywordNamesTheKey) {
  ReadKeyname run(NamesKey("\"acme-2026\""));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.Keyname().defaulted);
  EXPECT_EQ(run.Keyname().value, "acme-2026");
}

// §34.5.12.1: a string is one written thing however many words are inside it,
// so a key named with spaces is one value and not several expressions.
TEST(ProtectDataKeynameSyntax, AKeyNameHoldingSpacesIsOneValue) {
  ReadKeyname run(NamesKey("\"the 2026 signing key\""));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Keyname().value, "the 2026 signing key");
}

// §22.5.1 admits a bare identifier as a pragma_value, and one written thing is
// what this keyword is defined with, so a key named without quotation marks is
// named.
TEST(ProtectDataKeynameSyntax, ABareIdentifierIsOneWrittenThingToo) {
  ReadKeyname run(NamesKey("acme_2026"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Keyname().value, "acme_2026");
}

// §34.5.12.1 defines the expression with a string, and §22.5.1 makes a
// parenthesized pragma_value a list of further expressions rather than one
// written thing, so a list names no key. Naming none is not naming an empty
// one: the key the text named earlier still stands, an expression naming
// nothing having no standing to take it away.
TEST(ProtectDataKeynameSyntax, AListLeavesTheKeyAlreadyNamedStanding) {
  std::string src = NamesKey("\"acme-2026\"");
  src += NamesKey("(held_by=\"acme\")");
  ReadKeyname run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Keyname().value, "acme-2026");
}

// The same list where no key was named before it. It names none, so the keyword
// stands at its default -- which is what makes the case above about the list
// rather than about the value that happened to precede it.
TEST(ProtectDataKeynameSyntax, AListOnItsOwnNamesNoKey) {
  ReadKeyname run(NamesKey("(held_by=\"acme\")"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Keyname().defaulted);
}

// The '=' written with nothing after it. The spelling this keyword is defined
// in has a value against the '=', so a directive without one is no expression
// at all and §22.11 reports it.
TEST(ProtectDataKeynameSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect data_keyname =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

}  // namespace
