#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_preprocessor.h"
#include "helpers_delay_mode_directives.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

TEST(Preprocessor, DelayModePath_RecognizedBeforeModule) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`delay_mode_path\n"
                           "module t;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kPath);
}

TEST(Preprocessor, DelayModePath_DefaultStateNoDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "module t;\nendmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kNone);
}

TEST(Preprocessor, DelayModePath_IllegalInsideModule) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module t;\n"
                           "`delay_mode_path\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`delay_mode_path illegal inside a design element",
                            2, "E.5"));
}

TEST(Preprocessor, DelayModePath_LegalBetweenModules) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module a;\n"
                           "endmodule\n"
                           "`delay_mode_path\n"
                           "module b;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kPath);
}

TEST(Preprocessor, DelayModePath_SupersedesEarlierMode) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`delay_mode_distributed\n"
                           "`delay_mode_path\n"
                           "module t;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kPath);
}

TEST(Preprocessor, DelayModePath_RecordedAtEachModuleHeader) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`delay_mode_distributed\n"
                           "module spread;\n"
                           "endmodule\n"
                           "`delay_mode_path\n"
                           "module pathed;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& recorded = pp.ModuleDirectivesList();
  ASSERT_EQ(recorded.size(), 2u);
  EXPECT_EQ(recorded[0].module, "spread");
  EXPECT_EQ(recorded[0].delay_mode, DelayModeDirective::kDistributed);
  EXPECT_EQ(recorded[1].module, "pathed");
  EXPECT_EQ(recorded[1].delay_mode, DelayModeDirective::kPath);
}

TEST(Preprocessor, DelayModePath_CommentAfterItIsNoArgument) {
  ExpectCommentAfterItIsNoArgument(kPathDirective);
}

TEST(Preprocessor, DISABLED_DelayModePath_ALongerNameIsAMacroUse) {
  ExpectALongerNameIsAMacroUse(kPathDirective);
}

TEST(Preprocessor, DelayModePath_RecordedForAMacromodule) {
  ExpectRecordedForAMacromodule(kPathDirective);
}

TEST(Preprocessor, DelayModePath_ReadFromAnIncludedHeader) {
  ExpectReadFromAnIncludedHeader(kPathDirective);
}

TEST(Preprocessor, DelayModePath_CarriedIntoALaterFile) {
  ExpectCarriedIntoALaterFile(kPathDirective);
}

TEST(Preprocessor, DelayModePath_ReportedAnywhereInAModuleDeclaration) {
  ExpectReportedAnywhereInAModuleDeclaration(kPathDirective);
}

TEST(Preprocessor,
     DISABLED_DelayModePath_AcceptedInsideAnInterfaceProgramOrPackage) {
  ExpectAcceptedInsideAnInterfaceProgramOrPackage(kPathDirective);
}

TEST(Preprocessor, DelayModePath_AcceptedInsideAClass) {
  ExpectAcceptedInsideAClass(kPathDirective);
}

TEST(Preprocessor, DelayModePath_AfterTheLastModuleSetsNoModule) {
  ExpectAfterTheLastModuleSetsNoModule(kPathDirective);
}

}  // namespace
