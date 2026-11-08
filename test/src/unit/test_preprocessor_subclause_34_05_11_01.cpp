#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

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

TEST_F(ProtectDataMethodSyntaxTest, PragmaProtectDataMethodConsumed) {
  auto result = Preprocess("`pragma protect data_method = \"aes128-cbc\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("aes128-cbc"), std::string::npos);
}

TEST_F(ProtectDataMethodSyntaxTest,
       DataMethodDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect data_method = \"aes128-cbc\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST_F(ProtectDataMethodSyntaxTest,
       DataMethodStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect data_method = \"my custom cipher\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("my custom cipher"), std::string::npos);
}

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

std::string StatesMethod(std::string_view value) {
  std::string directive = "`pragma protect data_method=";
  directive.append(value).append("\n");
  return directive;
}

TEST(ProtectDataMethodSyntax, TheStringAgainstTheKeywordStatesTheAlgorithm) {
  ReadMethod run(StatesMethod("\"aes128-cbc\""));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.Method().defaulted);
  EXPECT_EQ(run.Method().value, "aes128-cbc");
}

TEST(ProtectDataMethodSyntax, AnAlgorithmNameHoldingSpacesIsOneValue) {
  ReadMethod run(StatesMethod("\"my custom cipher\""));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Method().value, "my custom cipher");
}

TEST(ProtectDataMethodSyntax, ABareIdentifierIsOneWrittenThingToo) {
  ReadMethod run(StatesMethod("aes128_cbc"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Method().value, "aes128_cbc");
}

TEST(ProtectDataMethodSyntax, AListLeavesTheAlgorithmAlreadyStatedStanding) {
  std::string src = StatesMethod("\"aes128-cbc\"");
  src += StatesMethod("(enctype=\"base64\")");
  ReadMethod run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Method().value, "aes128-cbc");
}

TEST(ProtectDataMethodSyntax, AListOnItsOwnStatesNoAlgorithm) {
  ReadMethod run(StatesMethod("(enctype=\"base64\")"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Method().defaulted);
}

TEST(ProtectDataMethodSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect data_method =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

}  // namespace
