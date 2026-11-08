#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

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

TEST_F(ProtectDigestKeyownerSyntaxTest, PragmaProtectDigestKeyownerConsumed) {
  auto result = Preprocess("`pragma protect digest_keyowner = \"Acme Corp\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("Acme Corp"), std::string::npos);
}

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

TEST(ProtectDigestKeyownerSyntax, TheStringAgainstTheKeywordNamesTheEntity) {
  EXPECT_EQ(
      ScopeFor(NamesDigestEntity("\"Acme Corp\""), "digest_keyowner").value,
      "Acme Corp");
}

TEST(ProtectDigestKeyownerSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(ScopeFor(NamesDigestEntity("acme_corp"), "digest_keyowner").value,
            "acme_corp");
}

TEST(ProtectDigestKeyownerSyntax, AListNamesNoEntityAndLeavesTheDefault) {
  std::string src = "`pragma protect data_keyowner=\"Acme Corp\"\n";
  src += NamesDigestEntity("(division=\"Widgets\")");
  EXPECT_TRUE(ScopeFor(src, "digest_keyowner").defaulted);
}

TEST(ProtectDigestKeyownerSyntax, AListOnItsOwnNamesNoEntity) {
  EXPECT_TRUE(
      ScopeFor(NamesDigestEntity("(division=\"Widgets\")"), "digest_keyowner")
          .defaulted);
}

}  // namespace
