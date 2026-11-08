#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

TEST(Preprocessor, DelayModeDistributed_RecognizedBeforeModule) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`delay_mode_distributed\n"
                           "module t;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kDistributed);
}

TEST(Preprocessor, DelayMode_DefaultStateNoDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "module t;\nendmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kNone);
}

TEST(Preprocessor, DelayModeDistributed_IllegalInsideModule) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module t;\n"
                           "`delay_mode_distributed\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "`delay_mode_distributed illegal inside a design element", 2, "E.4"));
}

TEST(Preprocessor, DelayModeDistributed_LegalBetweenModules) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module a;\n"
                           "endmodule\n"
                           "`delay_mode_distributed\n"
                           "module b;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kDistributed);
}

TEST(Preprocessor, DelayModeDistributed_RecordedAtEachModuleHeader) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module a;\n"
                           "endmodule\n"
                           "`delay_mode_distributed\n"
                           "module b;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& list = pp.ModuleDirectivesList();
  ASSERT_EQ(list.size(), 2u);
  EXPECT_EQ(list[0].module, "a");
  EXPECT_EQ(list[0].delay_mode, DelayModeDirective::kNone);
  EXPECT_EQ(list[1].module, "b");
  EXPECT_EQ(list[1].delay_mode, DelayModeDirective::kDistributed);
}

}  // namespace
