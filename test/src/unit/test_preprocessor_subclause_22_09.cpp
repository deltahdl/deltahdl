#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "invalid `unconnected_drive argument: 'pullx'", 1,
                            "22.9"));
}

// §22.9: `unconnected_drive requires one of the two arguments pull1 or pull0.
// The closest rejected input to the accepting form is the directive with no
// argument at all; the drive state stays at the default.
TEST(Preprocessor, UnconnectedDrive_MissingArg) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`unconnected_drive\n", f, pp);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "invalid `unconnected_drive argument: ''", 1,
                            "22.9"));
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kWire);
}

TEST(Preprocessor, Resetall_ClearsUnconnectedDrive) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`unconnected_drive pull1\n", f, pp);
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kTri1);
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kWire);
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "`unconnected_drive illegal inside a design element", 2, "22.9"));
}

TEST(Preprocessor, NounconnectedDrive_InsideModule_Error) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module t;\n`nounconnected_drive\nendmodule\n", f, pp);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "`nounconnected_drive illegal inside a design element", 2, "22.9"));
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

// §22.2 lets a directive whose syntax has a defined end be followed by another
// language element on the same line, and §22.9 gives `nounconnected_drive no
// argument, so its end is the directive name itself and the declaration after
// it is source text. This case is what confines the argument check below to
// the two strength keywords: any other text after the directive is a language
// element for the parser to judge.
TEST(Preprocessor, NounconnectedDrive_TrailingContent) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP("`nounconnected_drive wire x;\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("wire x;"), std::string::npos);
}

// §22.9 gives `unconnected_drive one of the arguments pull1 or pull0 and gives
// `nounconnected_drive none, so a strength keyword after the latter is an
// argument the directive does not take, reported on the directive's line by
// the preprocessor rather than handed to the parser as a stray keyword. The
// argument is consumed with the directive, so nothing reaches the output.
TEST(Preprocessor, NounconnectedDrive_Pull0ArgumentRejected) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP("`nounconnected_drive pull0\n", f, pp);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "`nounconnected_drive takes no argument; 'pull0' was given", 1, "22.9"));
  auto trimmed = out;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_TRUE(trimmed.empty());
}

// The other strength keyword, and the §22.2 allowance after it: the language
// element that follows the rejected argument still reaches the output.
TEST(Preprocessor, NounconnectedDrive_Pull1ArgumentRejected) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out = PreprocessWithPP("`nounconnected_drive pull1 wire x;\n", f, pp);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "`nounconnected_drive takes no argument; 'pull1' was given", 1, "22.9"));
  EXPECT_NE(out.find("wire x;"), std::string::npos);
  EXPECT_EQ(out.find("pull1"), std::string::npos);
}
