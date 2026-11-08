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

TEST_F(ProtectDataKeynameSyntaxTest, PragmaProtectDataKeynameConsumed) {
  auto result = Preprocess("`pragma protect data_keyname = \"primary-key\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("primary-key"), std::string::npos);
}

TEST_F(ProtectDataKeynameSyntaxTest,
       DataKeynameDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect data_keyname = \"primary-key\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST_F(ProtectDataKeynameSyntaxTest,
       DataKeynameStringArgumentWithSpacesConsumed) {
  auto result = Preprocess("`pragma protect data_keyname = \"my key name\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("my key name"), std::string::npos);
}

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

std::string NamesKey(std::string_view value) {
  std::string directive = "`pragma protect data_keyname=";
  directive.append(value).append("\n");
  return directive;
}

TEST(ProtectDataKeynameSyntax, TheStringAgainstTheKeywordNamesTheKey) {
  ReadKeyname run(NamesKey("\"acme-2026\""));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.Keyname().defaulted);
  EXPECT_EQ(run.Keyname().value, "acme-2026");
}

TEST(ProtectDataKeynameSyntax, AKeyNameHoldingSpacesIsOneValue) {
  ReadKeyname run(NamesKey("\"the 2026 signing key\""));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Keyname().value, "the 2026 signing key");
}

TEST(ProtectDataKeynameSyntax, ABareIdentifierIsOneWrittenThingToo) {
  ReadKeyname run(NamesKey("acme_2026"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Keyname().value, "acme_2026");
}

TEST(ProtectDataKeynameSyntax, AListLeavesTheKeyAlreadyNamedStanding) {
  std::string src = NamesKey("\"acme-2026\"");
  src += NamesKey("(held_by=\"acme\")");
  ReadKeyname run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Keyname().value, "acme-2026");
}

TEST(ProtectDataKeynameSyntax, AListOnItsOwnNamesNoKey) {
  ReadKeyname run(NamesKey("(held_by=\"acme\")"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Keyname().defaulted);
}

TEST(ProtectDataKeynameSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect data_keyname =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

}  // namespace
