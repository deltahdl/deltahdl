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

TEST_F(ProtectedTest, BeginEndEnvelope) {
  auto result = Preprocess(
      "module m;\n"
      "`pragma protect begin\n"
      "  logic secret_wire;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());

  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("logic secret_wire;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);

  EXPECT_EQ(result.find("pragma"), std::string::npos);
}

}
