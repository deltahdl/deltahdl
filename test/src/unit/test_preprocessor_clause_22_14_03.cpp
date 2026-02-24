// §22.14.3: IEEE Std 1364-2001 keywords

#include <gtest/gtest.h>
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"
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
// --- begin_keywords / end_keywords tests (IEEE 1800-2023 §22.14) ---
TEST(Preprocessor, BeginKeywords_EmitsMarker) {
  PreprocFixture f;
  auto result = Preprocess("`begin_keywords \"1364-2001\"\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  // Marker: \x01 + version byte (1 = kVer13642001) + \n
  std::string expected = {kKeywordMarker, '\x01', '\n'};
  EXPECT_NE(result.find(expected), std::string::npos);
}

}  // namespace
