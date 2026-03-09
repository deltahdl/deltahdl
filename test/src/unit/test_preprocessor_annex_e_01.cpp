#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_preprocessor.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

namespace {

TEST(Preprocessor, DefaultDecayTime_IntegerConstant) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_decay_time 100\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultDecayTime(), 100);
  EXPECT_FALSE(pp.DefaultDecayTimeInfinite());
}

TEST(Preprocessor, DefaultDecayTime_Zero) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_decay_time 0\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultDecayTime(), 0);
}

TEST(Preprocessor, DefaultDecayTime_RealConstant) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_decay_time 1.5\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_DOUBLE_EQ(pp.DefaultDecayTimeReal(), 1.5);
  EXPECT_FALSE(pp.DefaultDecayTimeInfinite());
}

TEST(Preprocessor, DefaultDecayTime_Infinite) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_decay_time infinite\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.DefaultDecayTimeInfinite());
}

TEST(Preprocessor, DefaultDecayTime_MissingArgument) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_decay_time\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DefaultDecayTime_InvalidArgument) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_decay_time abc\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DefaultDecayTime_NegativeValue) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_decay_time -5\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DefaultDecayTime_LaterOverrides) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_decay_time 100\n`default_decay_time 200\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultDecayTime(), 200);
}

TEST(Preprocessor, DefaultDecayTime_LargeInteger) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_decay_time 1000000\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultDecayTime(), 1000000u);
  EXPECT_FALSE(pp.DefaultDecayTimeInfinite());
}

TEST(Preprocessor, DefaultDecayTime_InfiniteToFinite) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`default_decay_time infinite\n"
      "`default_decay_time 42\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultDecayTime(), 42u);
  EXPECT_FALSE(pp.DefaultDecayTimeInfinite());
}

TEST(Preprocessor, DefaultDecayTime_FiniteToInfinite) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`default_decay_time 42\n"
      "`default_decay_time infinite\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.DefaultDecayTimeInfinite());
}

TEST(Preprocessor, DefaultDecayTime_RealFractional) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_decay_time 99.75\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_DOUBLE_EQ(pp.DefaultDecayTimeReal(), 99.75);
  EXPECT_EQ(pp.DefaultDecayTime(), 99u);
}

TEST(Preprocessor, DefaultDecayTime_IllegalInsideDesignElement) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module m;\n`default_decay_time 10\nendmodule\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DefaultTriregStrength_Valid) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_trireg_strength 50\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultTriregStrength(), 50u);
}

TEST(Preprocessor, DefaultTriregStrength_Zero) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_trireg_strength 0\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultTriregStrength(), 0u);
}

TEST(Preprocessor, DefaultTriregStrength_Max250) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_trireg_strength 250\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultTriregStrength(), 250u);
}

TEST(Preprocessor, DefaultTriregStrength_Above250) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_trireg_strength 251\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DefaultTriregStrength_LargeValue) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_trireg_strength 1000\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DefaultTriregStrength_MissingArgument) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_trireg_strength\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DefaultTriregStrength_InvalidArgument) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_trireg_strength abc\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DefaultTriregStrength_IllegalInsideDesignElement) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module m;\n`default_trireg_strength 50\nendmodule\n", f,
                   pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DefaultTriregStrength_LaterOverrides) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`default_trireg_strength 50\n`default_trireg_strength 100\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultTriregStrength(), 100u);
}

TEST(Preprocessor, DelayModeDistributed) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`delay_mode_distributed\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kDistributed);
}

TEST(Preprocessor, DelayModeDistributed_IllegalInsideDesignElement) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module m;\n`delay_mode_distributed\nendmodule\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DelayModePath) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`delay_mode_path\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kPath);
}

TEST(Preprocessor, DelayModePath_IllegalInsideDesignElement) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module m;\n`delay_mode_path\nendmodule\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DelayModeUnit) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`delay_mode_unit\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kUnit);
}

TEST(Preprocessor, DelayModeUnit_IllegalInsideDesignElement) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module m;\n`delay_mode_unit\nendmodule\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DelayModeZero) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`delay_mode_zero\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kZero);
}

TEST(Preprocessor, DelayModeZero_IllegalInsideDesignElement) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module m;\n`delay_mode_zero\nendmodule\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DelayMode_LastWins) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`delay_mode_distributed\n"
      "`delay_mode_path\n"
      "`delay_mode_unit\n"
      "`delay_mode_zero\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kZero);
}

TEST(Preprocessor, DelayMode_DefaultIsNone) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("// no directives\n", f, pp);
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kNone);
}

TEST(Preprocessor, AnnexE_AllDirectivesCombined) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`default_decay_time 10\n"
      "`default_trireg_strength 100\n"
      "`delay_mode_distributed\n"
      "module m; endmodule\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultDecayTime(), 10);
  EXPECT_EQ(pp.DefaultTriregStrength(), 100u);
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kDistributed);
}

TEST(Preprocessor, AnnexE_ResetallResetsState) {
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

TEST(Preprocessor, AnnexE_CannotRedefineAsMarco) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`define default_decay_time 42\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, AnnexE_CannotRedefineDelayModeDistributed) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`define delay_mode_distributed 1\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, AnnexE_DirectivesStrippedFromOutput) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto out =
      PreprocessWithPP("`default_decay_time 10\nmodule m; endmodule\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out.find("default_decay_time"), std::string::npos);
}

}  // namespace
