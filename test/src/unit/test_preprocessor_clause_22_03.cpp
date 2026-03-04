#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

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
