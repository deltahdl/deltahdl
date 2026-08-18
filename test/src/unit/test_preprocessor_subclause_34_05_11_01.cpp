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

// Exercises the syntax of the `data_method` protect pragma keyword
// (§34.5.11.1). The syntax block defines the keyword expression as
// `data_method = <string>`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including its string argument.
struct ProtectDataMethodSyntaxTest : ::testing::Test {
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

// The `data_method = <string>` keyword expression is accepted and the
// directive line is stripped, including its string value.
TEST_F(ProtectDataMethodSyntaxTest, PragmaProtectDataMethodConsumed) {
  auto result = Preprocess("`pragma protect data_method = \"aes128-cbc\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("aes128-cbc"), std::string::npos);
}

// Only the data_method directive line is removed; neighboring source text
// survives, confirming it is the data_method keyword expression line that the
// pragma path consumes.
TEST_F(ProtectDataMethodSyntaxTest,
       DataMethodDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect data_method = \"aes128-cbc\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// Edge case: the `<string>` value of the keyword expression may contain
// internal whitespace; the directive line is still consumed in full, with no
// portion of the quoted value leaking into the output.
TEST_F(ProtectDataMethodSyntaxTest,
       DataMethodStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect data_method = \"my custom cipher\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("my custom cipher"), std::string::npos);
}

// The three cases above observe the directive line going away, which any
// directive the pragma handler consumes does. What §34.5.11.1 defines is the
// value the expression states, so the cases below read that value back off the
// preprocessor once the whole text has passed through it: it belongs to the
// point the reading has reached rather than to any one line of output.

// A reading of `src` with the preprocessor kept alive afterwards.
struct ReadMethod {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, PreprocConfig{}};
  std::string text;

  explicit ReadMethod(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectKeywordValue Method() const {
    return pp.ProtectKeywords().ValueOf(kDataMethodKeyword);
  }
};

// One protect pragma directive writing `value` against the keyword exactly as
// given, so what stands against the '=' is what a case is about.
std::string StatesMethod(std::string_view value) {
  std::string directive = "`pragma protect data_method=";
  directive.append(value).append("\n");
  return directive;
}

// §34.5.11.1: the expression is `data_method = <string>`, and the string states
// the algorithm. The value in effect afterwards is what stood in the quotation
// marks, without them, and it is stated rather than defaulted.
TEST(ProtectDataMethodSyntax, TheStringAgainstTheKeywordStatesTheAlgorithm) {
  ReadMethod run(StatesMethod("\"aes128-cbc\""));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.Method().defaulted);
  EXPECT_EQ(run.Method().value, "aes128-cbc");
}

// §34.5.11.1: a string is one written thing however many words are inside it,
// so an algorithm named with spaces is one value and not several expressions.
TEST(ProtectDataMethodSyntax, AnAlgorithmNameHoldingSpacesIsOneValue) {
  ReadMethod run(StatesMethod("\"my custom cipher\""));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Method().value, "my custom cipher");
}

// §22.5.1 admits a bare identifier as a pragma_value, and one written thing is
// what this keyword is defined with, so an algorithm named without quotation
// marks is named.
TEST(ProtectDataMethodSyntax, ABareIdentifierIsOneWrittenThingToo) {
  ReadMethod run(StatesMethod("aes128_cbc"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Method().value, "aes128_cbc");
}

// §34.5.11.1 defines the expression with a string, and §22.5.1 makes a
// parenthesized pragma_value a list of further expressions rather than one
// written thing, so a list states no algorithm. Stating none is not stating an
// empty one: the algorithm the text stated earlier still stands, since an
// expression stating nothing has no standing to take it away.
TEST(ProtectDataMethodSyntax, AListLeavesTheAlgorithmAlreadyStatedStanding) {
  std::string src = StatesMethod("\"aes128-cbc\"");
  src += StatesMethod("(enctype=\"base64\")");
  ReadMethod run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Method().value, "aes128-cbc");
}

// The same list where no algorithm was stated before it. It states none, so the
// keyword stands at its default -- which is what makes the case above about the
// list rather than about the value that happened to precede it.
TEST(ProtectDataMethodSyntax, AListOnItsOwnStatesNoAlgorithm) {
  ReadMethod run(StatesMethod("(enctype=\"base64\")"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Method().defaulted);
}

// The '=' written with nothing after it. The spelling this keyword is defined
// in has a value against the '=', so a directive without one is no expression
// at all and §22.11 reports it.
TEST(ProtectDataMethodSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect data_method =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

}  // namespace
