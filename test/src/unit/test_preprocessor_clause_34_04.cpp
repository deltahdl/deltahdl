// §34.4: Protect pragma directives

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include <gtest/gtest.h>

using namespace delta;

struct ProtectedTest : ::testing::Test {
protected:
  std::string Preprocess(const std::string &src) {
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

TEST_F(ProtectedTest, PragmaProtectEndConsumed) {
  auto result = Preprocess("`pragma protect end\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// =============================================================================
// §34.5.1/2 Protected envelope begin/end parsing
// =============================================================================
TEST_F(ProtectedTest, BeginEndEnvelope) {
  auto result = Preprocess("module m;\n"
                           "`pragma protect begin\n"
                           "  logic secret_wire;\n"
                           "`pragma protect end\n"
                           "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  // Non-pragma lines should pass through.
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("logic secret_wire;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
  // Pragma lines consumed.
  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

// =============================================================================
// §34.5 Reset directive
// =============================================================================
TEST_F(ProtectedTest, ResetDirective) {
  auto result = Preprocess("`pragma protect begin\n"
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

} // namespace
