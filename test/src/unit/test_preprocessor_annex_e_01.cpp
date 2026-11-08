#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

constexpr const char* kAnnexEDirectives[] = {
    "default_decay_time", "default_trireg_strength", "delay_mode_distributed",
    "delay_mode_path",    "delay_mode_unit",         "delay_mode_zero",
};

TEST(OptionalCompilerDirectivesGeneral, TheSixListedNamesAreDirectives) {
  for (const char* name : kAnnexEDirectives) {
    EXPECT_TRUE(IsCompilerDirective(name)) << name;
  }
  EXPECT_FALSE(IsCompilerDirective("delay_mode_none"));
}

TEST(OptionalCompilerDirectivesGeneral, EachListedDirectiveIsCarriedOut) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`default_decay_time 100\n"
                           "`default_trireg_strength 120\n"
                           "`delay_mode_distributed\n"
                           "`delay_mode_path\n"
                           "`delay_mode_unit\n"
                           "`delay_mode_zero\n"
                           "module t;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultDecayTime(), 100u);
  EXPECT_EQ(pp.DefaultTriregStrength(), 120u);
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kZero);
}

TEST(OptionalCompilerDirectivesGeneral, ANameListedCannotNameAMacro) {
  for (const char* name : kAnnexEDirectives) {
    PreprocFixture f;
    Preprocess("`define " + std::string(name) + " 1\n", f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "redefining compiler directive '" + std::string(name) + "'", 1,
        "22.5.1"))
        << name;
  }
  PreprocFixture f;
  Preprocess("`define delay_mode_none 1\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
