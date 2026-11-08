#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

struct ProtectedTest : ::testing::Test {
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

TEST_F(ProtectedTest, AuthorInfoStringExpressionConsumed) {
  auto result =
      Preprocess("`pragma protect author_info = \"Acme IP Group, Rev 3\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("author_info"), std::string::npos);
}

TEST_F(ProtectedTest, AuthorInfoInEnvelopePreservesSource) {
  auto result = Preprocess(
      "module m;\n"
      "`pragma protect begin_protected\n"
      "`pragma protect author_info = \"contact: ip-support@example.com\"\n"
      "`pragma protect end_protected\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());

  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);

  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

TEST_F(ProtectedTest, AuthorInfoEmptyStringOperandConsumed) {
  auto result = Preprocess("`pragma protect author_info = \"\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("author_info"), std::string::npos);
}

struct DocumentedAuthor {
  SourceManager files;
  DiagEngine reports{files};
  Preprocessor reading{files, reports, PreprocConfig{}};
  std::string produced;

  explicit DocumentedAuthor(const std::string& src) {
    produced = reading.Preprocess(files.AddFile("<test>", src));
  }

  ProtectKeywordValue Documented() const {
    return reading.ProtectKeywords().ValueOf(kAuthorInfoKeyword);
  }
};

std::string Documents(std::string_view spelled) {
  std::string directive = "`pragma protect author_info=";
  directive.append(spelled).append("\n");
  return directive;
}

TEST(ProtectAuthorInfoSyntax,
     AListLeavesTheDocumentationAlreadyWrittenStanding) {
  std::string source = Documents("\"Acme IP Group, Rev 3\"");
  source += Documents("(team=\"Acme IP Group\", revision=\"3\")");
  DocumentedAuthor run(source);
  EXPECT_FALSE(run.reports.HasErrors());
  EXPECT_FALSE(run.Documented().defaulted);
  EXPECT_EQ(run.Documented().value, "Acme IP Group, Rev 3");
}

TEST(ProtectAuthorInfoSyntax,
     AListWithNothingDocumentedBeforeItLeavesTheDefault) {
  DocumentedAuthor run(Documents("(team=\"Acme IP Group\", revision=\"3\")"));
  EXPECT_FALSE(run.reports.HasErrors());
  EXPECT_TRUE(run.Documented().defaulted);
  EXPECT_TRUE(run.Documented().value.empty());
}

}  // namespace
