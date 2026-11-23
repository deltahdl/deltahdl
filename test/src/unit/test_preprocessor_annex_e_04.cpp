#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <utility>

#include "common/types.h"
#include "fixture_preprocessor.h"
#include "helpers_include_test_dir.h"
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

DelayModeDirective RecordedModeOf(const Preprocessor& pp,
                                  std::string_view module) {
  for (const auto& entry : pp.ModuleDirectivesList()) {
    if (entry.module == module) return entry.delay_mode;
  }
  return DelayModeDirective::kNone;
}

TEST(Preprocessor, DelayModeDistributed_RecordedForAMacromodule) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(f.mgr.AddFile("<test>",
                              "`delay_mode_distributed\n"
                              "macromodule m;\n"
                              "endmodule\n"));
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(pp.ModuleDirectivesList().size(), 1u);
  EXPECT_EQ(RecordedModeOf(pp, "m"), DelayModeDirective::kDistributed);
}

TEST(Preprocessor, DelayModeDistributed_ReadFromAnIncludedHeader) {
  IncludeTestDir tmp;
  tmp.WriteFile("mode.svh", "`delay_mode_distributed\n");
  std::string src =
      "module a;\n"
      "endmodule\n"
      "`include \"mode.svh\"\n"
      "module b;\n"
      "endmodule\n";
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(f.mgr.AddFile(tmp.WriteFile("main.sv", src).string(), src));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(RecordedModeOf(pp, "a"), DelayModeDirective::kNone);
  EXPECT_EQ(RecordedModeOf(pp, "b"), DelayModeDirective::kDistributed);
}

TEST(Preprocessor, DelayModeDistributed_IllegalAnywhereInAModuleDeclaration) {
  std::pair<const char*, int> cases[] = {
      {"module t(\n`delay_mode_distributed\n  input a);\nendmodule\n", 2},
      {"module o;\n  module n;\n`delay_mode_distributed\n  endmodule\n"
       "endmodule\n",
       3},
      {"module o;\n`delay_mode_distributed\n  module n;\n  endmodule\n"
       "endmodule\n",
       2},
      {"macromodule t;\n`delay_mode_distributed\nendmodule\n", 2},
  };
  for (const auto& [src, line] : cases) {
    PreprocFixture f;
    Preprocessor pp(f.mgr, f.diag, {});
    pp.Preprocess(f.mgr.AddFile("<test>", src));
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "`delay_mode_distributed illegal inside a design element", line, "E.4"))
        << src;
  }
}

TEST(
    Preprocessor,
    DISABLED_DelayModeDistributed_InsideAnInterfaceProgramOrPackageIsAccepted) {
  for (const char* element : {"interface", "program", "package"}) {
    std::string src = std::string(element) +
                      " e;\n`delay_mode_distributed\nend" + element +
                      "\nmodule m;\nendmodule\n";
    PreprocFixture f;
    Preprocessor pp(f.mgr, f.diag, {});
    pp.Preprocess(f.mgr.AddFile("<test>", src));
    EXPECT_TRUE(f.diag.Diagnostics().empty()) << element;
    EXPECT_EQ(RecordedModeOf(pp, "m"), DelayModeDirective::kDistributed)
        << element;
  }
}

}  // namespace
