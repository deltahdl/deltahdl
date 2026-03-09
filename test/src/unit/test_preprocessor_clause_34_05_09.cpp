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

TEST_F(ProtectedTest, ProtectedRegionWithEncoding) {
  auto result = Preprocess(
      "`pragma protect encoding=(enctype=\"raw\")\n"
      "`pragma protect data_method=\"x-caesar\"\n"
      "`pragma protect begin_protected\n"
      "`pragma protect data_block\n"
      "encrypted_data_here\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(diag_.HasErrors());

  EXPECT_EQ(result.find("pragma"), std::string::npos);

  EXPECT_NE(result.find("encrypted_data_here"), std::string::npos);
}

}  // namespace
