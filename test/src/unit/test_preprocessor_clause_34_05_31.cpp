// §34.5.31: reset

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
// §34.5 Reset directive
// =============================================================================
TEST_F(ProtectedTest, ResetDirective) {
  auto result = Preprocess(
      "`pragma protect begin\n"
      "  wire secret;\n"
      "`pragma protect end\n"
      "`pragma reset protect\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  // All pragma lines consumed. `pragma reset protect is also consumed.
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

}  // namespace
