#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

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

TEST_F(ProtectDataDecryptKeySyntaxTest, PragmaProtectDataDecryptKeyConsumed) {
  auto result = Preprocess("`pragma protect data_decrypt_key\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

TEST_F(ProtectDataDecryptKeySyntaxTest,
       DataDecryptKeyDirectiveStrippedSurroundingTextKept) {
  auto result =
      Preprocess("module m;\n`pragma protect data_decrypt_key\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

ProtectKeywordValue ScopeAfter(const std::string& src,
                               std::string_view keyword) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << src;
  return pp.ProtectKeywords().ValueOf(keyword);
}

TEST(ProtectDataDecryptKeySyntax, TheKeywordAloneCarriesNoKey) {
  EXPECT_TRUE(
      ScopeAfter("`pragma protect data_decrypt_key\n", "data_decrypt_key")
          .value.empty());
}

TEST(ProtectDataDecryptKeySyntax, TheKeywordAloneEndsAtTheComma) {
  EXPECT_EQ(
      ScopeAfter("`pragma protect data_decrypt_key, data_method=\"des-cbc\"\n",
                 "data_method")
          .value,
      "des-cbc");
}

TEST(ProtectDataDecryptKeySyntax, ALongerNameOpeningWithItIsADifferentName) {
  EXPECT_TRUE(ScopeAfter("`pragma protect data_decrypt_key_theirs=\"k\"\n",
                         "data_decrypt_key")
                  .defaulted);
}

TEST(ProtectDataDecryptKeySyntax, TheKeywordCarryingAValueSpeaksForNoLine) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  std::string read = pp.Preprocess(
      mgr.AddFile("<test>",
                  "`pragma protect begin_protected\n"
                  "`pragma protect data_decrypt_key=\"stated-here\"\n"
                  "wire beneath_w;\n"
                  "`pragma protect end_protected\n"));
  EXPECT_NE(read.find("wire beneath_w;"), std::string::npos) << read;
}

}  // namespace
