#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_preprocessor.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

TEST(Preprocessor, DefaultNettype_Wire) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype wire\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(Preprocessor, DefaultNettype_None) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype none\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  // §22.8: "none" forbids implicit net declarations.
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(Preprocessor, DefaultNettype_Tri) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype tri\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kTri);
}

// §22.8: `default_nettype trireg
TEST(Preprocessor, DefaultNettypeTrireg) {
  PreprocFixture f;
  Preprocess("`default_nettype trireg\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}
