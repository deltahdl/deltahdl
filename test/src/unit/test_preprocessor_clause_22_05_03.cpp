// §22.5.3: `undefineall

#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

static std::string Preprocess(const std::string& src, PreprocFixture& f,
                              PreprocConfig config = {}) {
  auto fid = f.mgr.AddFile("<test>", src);

  Preprocessor pp(f.mgr, f.diag, std::move(config));

  return pp.Preprocess(fid);

  namespace {

  // --- §22.5.3 `undefineall ---
  TEST(Preprocessor, UndefineAll) {
    PreprocFixture f;
    auto result = Preprocess(
        "`define FOO 42\n"
        "`undefineall\n"
        "`ifdef FOO\n"
        "visible\n"
        "`endif\n",
        f);
    EXPECT_EQ(result.find("visible"), std::string::npos);
  }

  }  // namespace
