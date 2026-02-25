#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct PreprocFixture {
  SourceManager mgr;
  DiagEngine diag{mgr};
};

static std::string Preprocess(const std::string& src, PreprocFixture& f,
                              PreprocConfig config = {}) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor pp(f.mgr, f.diag, std::move(config));
  return pp.Preprocess(fid);
}

TEST(Preprocessor, Include_AbsolutePath) {
  PreprocFixture f;
  auto result = Preprocess("`include \"/dev/null\"\nmodule m; endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

// §22.4: include filename with trailing comment
TEST(Preprocessor, IncludeFilenameStripsComment) {
  PreprocFixture f;
  // The include filename should stop at closing ", not consume comments
  Preprocess("`include \"nonexistent.sv\" // this is a comment\n", f);
  // Should error about "nonexistent.sv", not a garbled filename with comment
  EXPECT_TRUE(f.diag.HasErrors());
}
