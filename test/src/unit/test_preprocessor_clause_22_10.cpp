#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

TEST(Preprocessor, Celldefine_Toggle) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  EXPECT_FALSE(pp.InCelldefine());
  PreprocessWithPP("`celldefine\n", f, pp);
  EXPECT_TRUE(pp.InCelldefine());
  PreprocessWithPP("`endcelldefine\n", f, pp);
  EXPECT_FALSE(pp.InCelldefine());
}
