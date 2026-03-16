#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_preprocessor.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

TEST(Preprocessor, UnconnectedDrive_Pull0) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`unconnected_drive pull0\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kTri0);
}

TEST(Preprocessor, UnconnectedDrive_Pull1) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`unconnected_drive pull1\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kTri1);
}

TEST(Preprocessor, NounconnectedDrive_Reset) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`unconnected_drive pull1\n", f, pp);
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kTri1);
  PreprocessWithPP("`nounconnected_drive\n", f, pp);
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kWire);
}

TEST(Preprocessor, NounconnectedDrive_WithoutPrior_NoError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`nounconnected_drive\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kWire);
}

TEST(Preprocessor, UnconnectedDrive_InvalidArg) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`unconnected_drive pullx\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, UnconnectedDrive_MissingArg) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`unconnected_drive\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, UnconnectedDrive_MostRecentWins) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`unconnected_drive pull0\n", f, pp);
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kTri0);
  PreprocessWithPP("`unconnected_drive pull1\n", f, pp);
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kTri1);
}

TEST(Preprocessor, UnconnectedDrive_InsideModule_Error) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module t;\n`unconnected_drive pull0\nendmodule\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, NounconnectedDrive_InsideModule_Error) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module t;\n`nounconnected_drive\nendmodule\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, UnconnectedDrive_InsideInterface_Error) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("interface t;\n`unconnected_drive pull1\nendinterface\n", f,
                   pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, UnconnectedDrive_InsideProgram_Error) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("program t;\n`unconnected_drive pull1\nendprogram\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, UnconnectedDrive_NoOutput) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP("`unconnected_drive pull0\n", f, pp);
  auto trimmed = out;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_TRUE(trimmed.empty());
}

TEST(Preprocessor, NounconnectedDrive_NoOutput) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP("`nounconnected_drive\n", f, pp);
  auto trimmed = out;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_TRUE(trimmed.empty());
}

TEST(Preprocessor, NounconnectedDrive_TrailingContent) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP("`nounconnected_drive wire x;\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire x;"), std::string::npos);
}
