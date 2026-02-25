// §34.5.32: viewport

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
// §34.5 Viewport support
// =============================================================================
TEST_F(ProtectedTest, ViewportPragma) {
  auto result = Preprocess(
      "`pragma protect viewport=all\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("viewport"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

}  // namespace
