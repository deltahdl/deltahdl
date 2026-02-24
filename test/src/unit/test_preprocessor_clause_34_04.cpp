// §34.4: Protect pragma directives

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
