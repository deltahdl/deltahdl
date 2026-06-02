#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "preprocessor/preprocessor.h"

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

// Syntax 34.5.6.1: the author_info protect pragma expression takes the form
// `author_info = <string>`. The preprocessor accepts and consumes it.
TEST_F(ProtectedTest, AuthorInfoStringExpressionConsumed) {
  auto result =
      Preprocess("`pragma protect author_info = \"Acme IP Group, Rev 3\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("author_info"), std::string::npos);
}

// Edge case: an empty string operand is still a well-formed author_info
// expression and is consumed by the preprocessor like any other.
TEST_F(ProtectedTest, AuthorInfoEmptyStringConsumed) {
  auto result = Preprocess("`pragma protect author_info = \"\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("author_info"), std::string::npos);
}

// The author_info expression carries arbitrary additional author text in its
// string operand without disturbing the surrounding design source.
TEST_F(ProtectedTest, AuthorInfoInEnvelopePreservesSource) {
  auto result = Preprocess(
      "module m;\n"
      "`pragma protect begin_protected\n"
      "`pragma protect author_info = \"contact: ip-support@example.com\"\n"
      "`pragma protect data_block\n"
      "encrypted_payload\n"
      "`pragma protect end_protected\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());

  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);

  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

}  // namespace
