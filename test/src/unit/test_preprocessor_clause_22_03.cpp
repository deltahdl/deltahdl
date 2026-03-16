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

TEST(Preprocessor, ResetAll_DoesNotAffectBeginKeywordsStack) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`begin_keywords \"1800-2023\"\n", f, pp);
  PreprocessWithPP("`resetall\n", f, pp);

  PreprocessWithPP("`end_keywords\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetAll_EndKeywordsWithoutBeginAfterResetallErrors) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`resetall\n", f, pp);
  PreprocessWithPP("`end_keywords\n", f, pp);

  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetAll_DoesNotAffectConditionalStack) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define COND 1\n"
      "`ifdef COND\n"
      "`resetall\n"
      "int x = 1;\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1"), std::string::npos);
}

TEST(Preprocessor, ResetAll_ResetsDefaultDecayTime) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_decay_time 100\n", f, pp);
  EXPECT_FALSE(pp.DefaultDecayTimeInfinite());
  EXPECT_EQ(pp.DefaultDecayTime(), 100u);
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_TRUE(pp.DefaultDecayTimeInfinite());
}

TEST(Preprocessor, ResetAll_ResetsDefaultTriregStrength) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_trireg_strength 200\n", f, pp);
  EXPECT_TRUE(pp.HasDefaultTriregStrength());
  EXPECT_EQ(pp.DefaultTriregStrength(), 200u);
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_FALSE(pp.HasDefaultTriregStrength());
}

TEST(Preprocessor, ResetAll_ResetsDelayModeDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`delay_mode_zero\n", f, pp);
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kZero);
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kNone);
}

TEST(Preprocessor, ResetAll_IllegalInsideNestedDesignElement) {
  PreprocFixture f;
  Preprocess(
      "module outer;\n"
      "  module inner;\n"
      "    `resetall\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetAll_MultipleConsecutiveLegal) {
  PreprocFixture f;
  Preprocess("`resetall\n`resetall\n`resetall\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetAll_BetweenDesignElementsLegal) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`default_nettype none\n"
                           "module m1; endmodule\n"
                           "`resetall\n"
                           "module m2; endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(Preprocessor, ResetAll_DoesNotAffectMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PERSIST 99\n"
      "`resetall\n"
      "int x = `PERSIST;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("99"), std::string::npos);
}

TEST(Preprocessor, ResetAll_ResetsMultipleDirectivesAtOnce) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`default_decay_time 50\n"
      "`default_trireg_strength 200\n"
      "`delay_mode_path\n"
      "`resetall\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultDecayTime(), 0);
  EXPECT_TRUE(pp.DefaultDecayTimeInfinite());
  EXPECT_EQ(pp.DefaultTriregStrength(), 0u);
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kNone);
}

TEST(Preprocessor, Pragma_Resetall_NoError) {
  PreprocFixture f;
  Preprocess("`pragma resetall\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Pragma_ResetallDoesNotAffectPragma) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`pragma some_pragma key=val\n", f, pp);
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetAll_InsideExcludedConditionalNotExecuted) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype none\n", f, pp);
  PreprocessWithPP(
      "`ifdef UNDEFINED_MACRO\n"
      "`resetall\n"
      "`endif\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

TEST(Preprocessor, ResetAll_IdempotentWhenAlreadyAtDefaults) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`resetall\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
  EXPECT_FALSE(pp.InCelldefine());
  EXPECT_FALSE(pp.HasTimescale());
  EXPECT_TRUE(pp.DefaultDecayTimeInfinite());
}

TEST(Preprocessor, ResetAll_DoesNotRestoreUndefMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define TEMP 1\n"
      "`undef TEMP\n"
      "`resetall\n"
      "`ifdef TEMP\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

TEST(Preprocessor, ResetAll_LegalAfterEndOfDesignElement) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`default_nettype none\n"
      "module m; endmodule\n"
      "`resetall\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(Preprocessor, ResetAll_ErrorInsideGenerateBlock) {
  PreprocFixture f;
  Preprocess(
      "module m;\n"
      "  generate\n"
      "    `resetall\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}
