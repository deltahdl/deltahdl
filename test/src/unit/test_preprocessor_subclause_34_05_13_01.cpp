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

// Exercises the syntax of the `data_public_key` protect pragma keyword
// (§34.5.13.1). The syntax block defines the keyword as the bare word
// `data_public_key` with no arguments. Protect pragmas are processed at the
// preprocessor stage, where the generic `pragma` handler recognizes the
// keyword and consumes the directive line.
struct ProtectDataPublicKeySyntaxTest : ::testing::Test {
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

// The bare `data_public_key` keyword is accepted and the directive line is
// stripped.
TEST_F(ProtectDataPublicKeySyntaxTest, PragmaProtectDataPublicKeyConsumed) {
  auto result = Preprocess("`pragma protect data_public_key\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the data_public_key directive line is removed; neighboring source text
// survives, confirming it is the data_public_key keyword line that the pragma
// path consumes.
TEST_F(ProtectDataPublicKeySyntaxTest,
       DataPublicKeyDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect data_public_key\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The two cases above observe the directive line going away, which any
// directive the pragma handler consumes does. What §34.5.13.1 defines is the
// spelling: the keyword stands alone, with nothing written against it. The
// cases below state that, reading back off the preprocessor what the keyword
// left in effect.

// A reading of `src` with the preprocessor kept alive afterwards.
struct ReadPublicKey {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, PreprocConfig{}};
  std::string text;

  explicit ReadPublicKey(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectKeywordValue ValueOf(std::string_view keyword) const {
    return pp.ProtectKeywords().ValueOf(keyword);
  }
};

// §34.5.13.1: the expression is the keyword and nothing else, so the keyword
// standing alone states no value of its own. What it does state is that the
// next line carries one, which is §34.5.13.2's rule and is read only inside a
// protected region; here there is none, so nothing is put in effect for it.
TEST(ProtectDataPublicKeySyntax, TheKeywordStandsAloneAndStatesNoValue) {
  ReadPublicKey run("`pragma protect data_public_key\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("data_public_key").defaulted);
}

// §22.11 writes a directive's expressions as a comma-separated list, and an
// expression that is a keyword standing alone is one of the forms that list
// admits. The expression beside it takes effect, so the bare keyword is read as
// an expression of the list rather than swallowing what follows it.
TEST(ProtectDataPublicKeySyntax, TheKeywordStandsAloneAmongOtherExpressions) {
  ReadPublicKey run(
      "`pragma protect data_public_key, data_keyname=\"acme-2026\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyname").value, "acme-2026");
}

// The same list with the bare keyword written last, which is the other place a
// list can put it. A reading that took the keyword for the start of a value
// would have nothing to end it with here.
TEST(ProtectDataPublicKeySyntax, TheKeywordStandsAloneLastInAList) {
  ReadPublicKey run(
      "`pragma protect data_keyname=\"acme-2026\", data_public_key\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyname").value, "acme-2026");
}

// The '=' written after the keyword with nothing following it. The spelling
// §34.5.13.1 defines has nothing after the keyword at all, and an '=' with no
// value after it is no pragma_expression in any spelling, so §22.11 reports it.
TEST(ProtectDataPublicKeySyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect data_public_key =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// The keyword written as an escaped identifier. §34.5.13.1 spells it as a
// simple identifier, and an escaped one is a different token, so what stands
// there is no pragma_keyword and the directive is no expression.
TEST(ProtectDataPublicKeySyntax, TheKeywordAsAnEscapedIdentifierIsRejected) {
  PreprocFixture f;
  Preprocess("`pragma protect \\data_public_key \n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

}  // namespace
