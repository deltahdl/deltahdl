#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_preprocessor.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

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

TEST(Preprocessor, ResetAll_IllegalInsideMacromodule) {
  PreprocFixture f;
  Preprocess("macromodule mm;\n`resetall\nendmodule\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetAll_ResetsDefaultNettype) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype none\n", f, pp);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(Preprocessor, ResetAll_ResetsCelldefine) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`celldefine\n", f, pp);
  EXPECT_TRUE(pp.InCelldefine());
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_FALSE(pp.InCelldefine());
}

TEST(Preprocessor, ResetAll_ResetsUnconnectedDrive) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`unconnected_drive pull1\n", f, pp);
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kTri1);
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kWire);
}

TEST(Preprocessor, ResetAll_ResetsTimescale) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns / 1ps\n", f, pp);
  EXPECT_TRUE(pp.HasTimescale());
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_FALSE(pp.HasTimescale());
}

TEST(Preprocessor, ResetAll_DoesNotAffectLineDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`line 42 \"foo.sv\" 0\n", f, pp);
  EXPECT_TRUE(pp.HasLineOverride());
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_TRUE(pp.HasLineOverride());
}
