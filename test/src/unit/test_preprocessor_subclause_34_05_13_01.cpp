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

TEST_F(ProtectDataPublicKeySyntaxTest, PragmaProtectDataPublicKeyConsumed) {
  auto result = Preprocess("`pragma protect data_public_key\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

TEST_F(ProtectDataPublicKeySyntaxTest,
       DataPublicKeyDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect data_public_key\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

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

TEST(ProtectDataPublicKeySyntax, TheKeywordStandsAloneAndDesignatesNothing) {
  ReadPublicKey run("`pragma protect data_public_key\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("data_public_key").value.empty());
}

TEST(ProtectDataPublicKeySyntax, TheKeywordStandsAloneAmongOtherExpressions) {
  ReadPublicKey run(
      "`pragma protect data_public_key, data_keyname=\"acme-2026\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyname").value, "acme-2026");
}

TEST(ProtectDataPublicKeySyntax, TheKeywordStandsAloneLastInAList) {
  ReadPublicKey run(
      "`pragma protect data_keyname=\"acme-2026\", data_public_key\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyname").value, "acme-2026");
}

TEST(ProtectDataPublicKeySyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect data_public_key =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectDataPublicKeySyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  ReadPublicKey run("`pragma protect data_public_key_of_theirs=\"k\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("data_public_key").defaulted);
}

TEST(ProtectDataPublicKeySyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  PreprocFixture f;
  std::string read = Preprocess(
      "`pragma protect begin_protected\n"
      "`pragma protect data_public_key=\"stated-here\"\n"
      "wire beneath_w;\n"
      "`pragma protect end_protected\n",
      f);
  EXPECT_NE(read.find("wire beneath_w;"), std::string::npos) << read;
}

}  // namespace
