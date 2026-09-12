#include <gtest/gtest.h>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"

using namespace delta;

// §E.4 `delay_mode_distributed. The directive selects the distributed delay
// mode for every module that follows it in the source description. It takes no
// argument, and it shall appear before the declaration of the module whose
// delay mode it controls. All three rules are carried by the preprocessor,
// which recognizes the directive, records the selected mode queried below, and
// rejects the directive when it appears inside a design element.

namespace {

// E4-C1/C2 (declarative + syntax): the bare directive is recognized before a
// module declaration and records the distributed delay mode for what follows.
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

// E4-C1 (baseline): with no directive present, no delay mode is in effect.
TEST(Preprocessor, DelayMode_DefaultStateNoDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "module t;\nendmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kNone);
}

// E4-C3 (shall): the directive shall precede the module declaration; placing it
// inside a design element is illegal and is rejected.
TEST(Preprocessor, DelayModeDistributed_IllegalInsideModule) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module t;\n"
                           "`delay_mode_distributed\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  // E.4 is where the standard says the directive comes before the module
  // it controls, so the report names it.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "`delay_mode_distributed illegal inside a design element", 2, "E.4"));
}

// E4-C3 (shall, boundary): once a module declaration has closed, the design
// element nesting is back at the top level, so the directive is legal again
// before the next module and records the mode for the module that follows.
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

// E.4 has the directive select the mode for the modules that follow it, so
// the record the preprocessor keeps of the directives in force at each module
// header carries no mode for a module declared before the directive and the
// distributed mode for the module declared after it, while the unit-wide
// query above answers only with the last directive.
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
