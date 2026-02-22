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

// §22.3: `resetall shall not affect text macros
TEST(Preprocessor, ResetAll_PreservesTextMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO bar\n"
      "`resetall\n"
      "int x = `FOO;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("bar"), std::string::npos);
}

// §3.2 + §22.3: `resetall is illegal inside ALL 7 design element types.
TEST(Preprocessor, ResetAll_IllegalInsideModule) {
  PreprocFixture f;
  Preprocess("module m;\n`resetall\nendmodule\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetAll_IllegalInsideProgram) {
  PreprocFixture f;
  Preprocess("program p;\n`resetall\nendprogram\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetAll_IllegalInsideInterface) {
  PreprocFixture f;
  Preprocess("interface ifc;\n`resetall\nendinterface\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetAll_IllegalInsideChecker) {
  PreprocFixture f;
  Preprocess("checker chk;\n`resetall\nendchecker\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetAll_IllegalInsidePackage) {
  PreprocFixture f;
  Preprocess("package pkg;\n`resetall\nendpackage\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetAll_IllegalInsidePrimitive) {
  PreprocFixture f;
  Preprocess("primitive udp(out, a);\n`resetall\nendprimitive\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetAll_IllegalInsideConfig) {
  PreprocFixture f;
  Preprocess("config cfg;\n`resetall\nendconfig\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetAll_LegalOutsideDesignElements) {
  PreprocFixture f;
  Preprocess(
      "`resetall\n"
      "module m; endmodule\n"
      "`resetall\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}
