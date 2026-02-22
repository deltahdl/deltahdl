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
}

// §22 Table 22-2: SV_COV_* predefined coverage macros
TEST(Preprocessor, SvCovPredefinedMacros) {
  PreprocFixture f;
  auto result = Preprocess("`ifdef SV_COV_START\n"
                           "cov_start_defined\n"
                           "`endif\n"
                           "val=`SV_COV_START\n",
                           f);
  EXPECT_NE(result.find("cov_start_defined"), std::string::npos);
  EXPECT_NE(result.find("val=0"), std::string::npos);
}

TEST(Preprocessor, SvCovToggleValue) {
  PreprocFixture f;
  auto result = Preprocess("x=`SV_COV_TOGGLE\n", f);
  EXPECT_NE(result.find("x=23"), std::string::npos);
}

TEST(Preprocessor, SvCovErrorValue) {
  PreprocFixture f;
  auto result = Preprocess("x=`SV_COV_ERROR\n", f);
  EXPECT_NE(result.find("x=-1"), std::string::npos);
}
