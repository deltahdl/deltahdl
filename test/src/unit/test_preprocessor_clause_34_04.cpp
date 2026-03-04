// §34.4: Protect pragma directives

#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
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

// =============================================================================
// §34.4 Pragma protect directive recognition
// =============================================================================
TEST_F(ProtectedTest, PragmaProtectConsumed) {
  auto result = Preprocess("`pragma protect begin\n");
  EXPECT_FALSE(diag_.HasErrors());
  // Pragma line should be consumed (not appear in output).
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

}  // namespace
