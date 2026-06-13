#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

// §E.6 `delay_mode_unit. The directive selects the unit delay mode for every
// module that follows it in the source description. It takes no argument, and
// it shall appear before the declaration of the module whose delay mode it
// controls. All three rules are carried by the preprocessor, which recognizes
// the directive, records the selected mode queried below, and rejects the
// directive when it appears inside a design element.

namespace {

// E6-C1/C2 (declarative + syntax): the bare directive is recognized before a
// module declaration and records the unit delay mode for what follows.
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

// E6-C1 (baseline): with no directive present, no delay mode is in effect.
TEST(Preprocessor, DelayModeUnit_DefaultStateNoDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "module t;\nendmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kNone);
}

// E6-C3 (shall): the directive shall precede the module declaration; placing it
// inside a design element is illegal and is rejected.
TEST(Preprocessor, DelayModeUnit_IllegalInsideModule) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module t;\n"
                           "`delay_mode_unit\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(f.diag.HasErrors());
}

// E6-C3 (shall, boundary): once a module declaration has closed, the design
// element nesting is back at the top level, so the directive is legal again
// before the next module and records the mode for the module that follows.
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

// E6-C1 (sequencing edge): the directive selects the unit delay mode for what
// follows it, so issuing it after a different mode directive supersedes that
// earlier mode. The recording stage ends with the unit mode in effect.
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

}  // namespace
