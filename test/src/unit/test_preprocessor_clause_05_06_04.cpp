#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_preprocessor.h"

using namespace delta;

namespace {

static std::string PreprocessFile(const std::string& path,
                                  const std::string& src, PreprocFixture& f,
                                  Preprocessor& pp) {
  auto fid = f.mgr.AddFile(path, src);
  return pp.Preprocess(fid);
}

TEST(CompilerDirectivePreprocessor, GraveAccentIntroducesDirective) {
  PreprocFixture f;

  std::string src = std::string("\x60") + "define X 42\n" + "\x60" + "X\n";
  auto result = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
}

TEST(CompilerDirectivePreprocessor, NoGraveAccentNoDirective) {
  PreprocFixture f;
  auto result = Preprocess("define X 42\n", f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("define X 42"), std::string::npos);
}

TEST(CompilerDirectivePreprocessor, DirectivePersistsAcrossSameCu) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessFile("a.sv", "`default_nettype none\n", f, pp);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);

  PreprocessFile("b.sv", "module m; endmodule\n", f, pp);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(CompilerDirectivePreprocessor, DirectiveOverriddenByLaterDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessFile("a.sv", "`default_nettype none\n", f, pp);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
  PreprocessFile("b.sv", "`default_nettype wire\n", f, pp);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(CompilerDirectivePreprocessor, DefineInOneFileVisibleInAnother) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessFile("a.sv", "`define WIDTH 16\n", f, pp);
  auto result = PreprocessFile("b.sv", "localparam W = `WIDTH;\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("16"), std::string::npos);
}

TEST(CompilerDirectivePreprocessor, MacroDefinedInOneCuInvisibleInOther) {
  {
    PreprocFixture f;
    Preprocessor cu1(f.mgr, f.diag, {});
    PreprocessFile("cu1.sv", "`define ONLY_IN_CU1 1\n", f, cu1);
    EXPECT_FALSE(f.diag.HasErrors());
  }

  PreprocFixture f2;
  Preprocessor cu2(f2.mgr, f2.diag, {});
  auto result = PreprocessFile(
      "cu2.sv", "`ifdef ONLY_IN_CU1\nleaked\n`else\nisolated\n`endif\n", f2,
      cu2);
  EXPECT_FALSE(f2.diag.HasErrors());
  EXPECT_EQ(result.find("leaked"), std::string::npos);
  EXPECT_NE(result.find("isolated"), std::string::npos);
}

TEST(CompilerDirectivePreprocessor, DefineAffectsOnlySubsequentReads) {
  PreprocFixture f;
  std::string src = std::string("\x60") + "ifdef X\nEARLY_BRANCH\n" + "\x60" +
                    "else\nEARLY_ELSE\n" + "\x60" + "endif\n" + "\x60" +
                    "define X 1\n" + "\x60" + "ifdef X\nLATE_BRANCH\n" +
                    "\x60" + "else\nLATE_ELSE\n" + "\x60" + "endif\n";
  auto result = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("EARLY_BRANCH"), std::string::npos);
  EXPECT_NE(result.find("EARLY_ELSE"), std::string::npos);
  EXPECT_NE(result.find("LATE_BRANCH"), std::string::npos);
  EXPECT_EQ(result.find("LATE_ELSE"), std::string::npos);
}

TEST(CompilerDirectivePreprocessor, ConcurrentCusIndependent) {
  PreprocFixture f;
  Preprocessor cu1(f.mgr, f.diag, {});
  Preprocessor cu2(f.mgr, f.diag, {});
  PreprocessFile("cu1.sv", "`default_nettype none\n", f, cu1);
  PreprocessFile("cu2.sv", "`default_nettype tri\n", f, cu2);
  EXPECT_EQ(cu1.DefaultNetType(), NetType::kNone);
  EXPECT_EQ(cu2.DefaultNetType(), NetType::kTri);
}

}  // namespace
