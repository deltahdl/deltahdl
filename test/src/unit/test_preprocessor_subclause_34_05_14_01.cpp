#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

// Exercises the syntax of the `data_decrypt_key` protect pragma keyword
// (§34.5.14.1). The syntax block defines the keyword as the bare word
// `data_decrypt_key` with no arguments. Protect pragmas are processed at the
// preprocessor stage, where the generic `pragma` handler recognizes the
// keyword and consumes the directive line.
struct ProtectDataDecryptKeySyntaxTest : ::testing::Test {
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

// The bare `data_decrypt_key` keyword is accepted and the directive line is
// stripped.
TEST_F(ProtectDataDecryptKeySyntaxTest, PragmaProtectDataDecryptKeyConsumed) {
  auto result = Preprocess("`pragma protect data_decrypt_key\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// Only the data_decrypt_key directive line is removed; neighboring source text
// survives, confirming it is the data_decrypt_key keyword line that the pragma
// path consumes.
TEST_F(ProtectDataDecryptKeySyntaxTest,
       DataDecryptKeyDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect data_decrypt_key\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The two cases above observe the directive line going away, which any
// directive the pragma handler consumes does. What §34.5.14.1 defines is the
// spelling: the keyword and nothing else. The cases below hold a text to it by
// reading the keyword scope the run left behind, since a spelling that was not
// recognized leaves nothing there.

// What the protect pragma keyword scope holds for `keyword` after reading
// `src`. The scope is the whole of what a syntax case can observe of a keyword
// that carries no value: it says whether the reading took the word for the
// keyword at all.
ProtectKeywordValue ScopeAfter(const std::string& src,
                               std::string_view keyword) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << src;
  return pp.ProtectKeywords().ValueOf(keyword);
}

// §34.5.14.1: the expression is the keyword alone, so it carries no value to
// designate a key with. The value it announces arrives on the line beneath it,
// which §34.5.14.2 reads and only inside a protected region; there is none
// here, so the keyword leaves nothing to designate anything with.
TEST(ProtectDataDecryptKeySyntax, TheKeywordAloneCarriesNoKey) {
  EXPECT_TRUE(
      ScopeAfter("`pragma protect data_decrypt_key\n", "data_decrypt_key")
          .value.empty());
}

// The keyword written as one expression of §22.11's comma-separated list, with
// a second expression after it. That expression takes effect, so the keyword
// standing alone ends where the comma does rather than running on into it.
TEST(ProtectDataDecryptKeySyntax, TheKeywordAloneEndsAtTheComma) {
  EXPECT_EQ(
      ScopeAfter("`pragma protect data_decrypt_key, data_method=\"des-cbc\"\n",
                 "data_method")
          .value,
      "des-cbc");
}

// §34.5.14.1 spells one name. A longer name opening with those characters is a
// different one, which §34.4 does not tabulate, so nothing is put in effect for
// the name it resembles.
TEST(ProtectDataDecryptKeySyntax, ALongerNameOpeningWithItIsADifferentName) {
  EXPECT_TRUE(ScopeAfter("`pragma protect data_decrypt_key_theirs=\"k\"\n",
                         "data_decrypt_key")
                  .defaulted);
}

}  // namespace
