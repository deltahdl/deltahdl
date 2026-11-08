#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

TEST(Preprocessor, DelayModeUnit_RecognizedBeforeModule) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`delay_mode_unit\n"
                           "module t;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kUnit);
}

TEST(Preprocessor, DelayModeUnit_DefaultStateNoDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "module t;\nendmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kNone);
}

TEST(Preprocessor, DelayModeUnit_IllegalInsideModule) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module t;\n"
                           "`delay_mode_unit\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`delay_mode_unit illegal inside a design element",
                            2, "E.6"));
}

TEST(Preprocessor, DelayModeUnit_LegalBetweenModules) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module a;\n"
                           "endmodule\n"
                           "`delay_mode_unit\n"
                           "module b;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kUnit);
}

TEST(Preprocessor, DelayModeUnit_SupersedesEarlierMode) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`delay_mode_path\n"
                           "`delay_mode_unit\n"
                           "module t;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kUnit);
}

TEST(Preprocessor, DelayModeUnit_RecordedAtEachModuleHeader) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`delay_mode_path\n"
                           "module routed;\n"
                           "endmodule\n"
                           "`delay_mode_unit\n"
                           "module stepped;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& at_headers = pp.ModuleDirectivesList();
  ASSERT_EQ(at_headers.size(), 2u);
  EXPECT_EQ(at_headers[0].module, "routed");
  EXPECT_EQ(at_headers[0].delay_mode, DelayModeDirective::kPath);
  EXPECT_EQ(at_headers[1].module, "stepped");
  EXPECT_EQ(at_headers[1].delay_mode, DelayModeDirective::kUnit);
}

}  // namespace
