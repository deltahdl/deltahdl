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

TEST(Preprocessor, FileExpansion) {
  PreprocFixture f;
  auto result = Preprocess("`__FILE__\n", f);
  EXPECT_NE(result.find("\"<test>\""), std::string::npos);
}

TEST(Preprocessor, LineExpansion) {
  PreprocFixture f;
  auto result = Preprocess(
      "line1\n"
      "`__LINE__\n",
      f);
  EXPECT_NE(result.find('2'), std::string::npos);
}

// --- __LINE__ with `line directive ---

TEST(Preprocessor, LineDirectiveAffectsLineMacro) {
  PreprocFixture f;
  auto result = Preprocess(
      "`line 100 \"test.sv\" 0\n"
      "`__LINE__\n",
      f);
  EXPECT_NE(result.find("101"), std::string::npos);
}

TEST(Preprocessor, InlineMacro_ExpandsFileInline) {
  PreprocFixture f;
  auto result = Preprocess("$display(`__FILE__);\n", f);
  EXPECT_NE(result.find("$display(\"<test>\");"), std::string::npos);
}

TEST(Preprocessor, InlineMacro_ExpandsLineInline) {
  PreprocFixture f;
  auto result = Preprocess("$display(`__LINE__);\n", f);
  EXPECT_NE(result.find("$display(1);"), std::string::npos);
}
