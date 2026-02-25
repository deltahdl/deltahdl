// §34.5.28: decrypt_license

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

TEST_F(ProtectedTest, DecryptLicensePragma) {
  auto result = Preprocess(
      "`pragma protect decrypt_license=(library=\"lic.so\","
      "feature=\"decryptIP\")\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("decrypt_license"), std::string::npos);
}

}  // namespace
