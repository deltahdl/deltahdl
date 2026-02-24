// §34.5.1: begin

#include <gtest/gtest.h>
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct PreprocFixture {
  SourceManager mgr;
  DiagEngine diag{mgr};
};

static std::string Preprocess(const std::string &src, PreprocFixture &f,
                              PreprocConfig config = {}) {

  auto fid = f.mgr.AddFile("<test>", src);

  Preprocessor pp(f.mgr, f.diag, std::move(config));

  return pp.Preprocess(fid);

namespace {

}
TEST(Preprocessor, Pragma_Consumed) {
  PreprocFixture f;
  auto result = Preprocess("`pragma protect begin\ncode\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  // Pragma line should be consumed (not appear in output).
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("code"), std::string::npos);
}

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
