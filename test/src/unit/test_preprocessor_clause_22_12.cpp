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

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

TEST(Preprocessor, Line_OverridesLineNumber) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`line 42 \"foo.sv\" 0\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasLineOverride());
  EXPECT_EQ(pp.LineOffset(), 42);
}

// §22.12: `line directive validation
TEST(Preprocessor, Line_IllegalLevel) {
  PreprocFixture f;
  Preprocess("`line 1 \"somefile\" 3\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_NonStringFilename) {
  PreprocFixture f;
  Preprocess("`line 1 somefile 2\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_NegativeLineNumber) {
  PreprocFixture f;
  Preprocess("`line -12 \"somefile\" 3\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_MissingLevel) {
  PreprocFixture f;
  Preprocess("`line 1 \"somefile\"\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_MissingFilename) {
  PreprocFixture f;
  Preprocess("`line 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}
