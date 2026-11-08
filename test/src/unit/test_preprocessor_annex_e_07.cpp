#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

TEST(Preprocessor, DelayModeZero_RecognizedBeforeModule) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`delay_mode_zero\n"
                           "module t;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kZero);
}

TEST(Preprocessor, DelayModeZero_DefaultStateNoDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "module t;\nendmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kNone);
}

TEST(Preprocessor, DelayModeZero_IllegalInsideModule) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module t;\n"
                           "`delay_mode_zero\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`delay_mode_zero illegal inside a design element",
                            2, "E.7"));
}

TEST(Preprocessor, DelayModeZero_LegalBetweenModules) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module a;\n"
                           "endmodule\n"
                           "`delay_mode_zero\n"
                           "module b;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kZero);
}

TEST(Preprocessor, DelayModeZero_SupersedesEarlierMode) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`delay_mode_unit\n"
                           "`delay_mode_zero\n"
                           "module t;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kZero);
}

TEST(Preprocessor, DelayModeZero_RecordedAtEachModuleHeader) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`delay_mode_unit\n"
                           "module ticking;\n"
                           "endmodule\n"
                           "`delay_mode_zero\n"
                           "module instant;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& per_module = pp.ModuleDirectivesList();
  ASSERT_EQ(per_module.size(), 2u);
  EXPECT_EQ(per_module[0].module, "ticking");
  EXPECT_EQ(per_module[0].delay_mode, DelayModeDirective::kUnit);
  EXPECT_EQ(per_module[1].module, "instant");
  EXPECT_EQ(per_module[1].delay_mode, DelayModeDirective::kZero);
}

}  // namespace
