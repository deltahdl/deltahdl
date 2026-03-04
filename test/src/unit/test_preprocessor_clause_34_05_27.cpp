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

TEST_F(ProtectedTest, KeyBlockPragma) {
  auto result = Preprocess(
      "`pragma protect key_keyowner=\"Acme\"\n"
      "`pragma protect key_method=\"rsa\"\n"
      "`pragma protect key_block\n"
      "base64encodedkeydata\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(diag_.HasErrors());

  EXPECT_EQ(result.find("key_keyowner"), std::string::npos);
  EXPECT_EQ(result.find("key_method"), std::string::npos);
}

}
