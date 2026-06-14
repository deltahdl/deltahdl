#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

// §E.7 `delay_mode_zero. The directive selects the zero delay mode for every
// module that follows it in the source description. It takes no argument, and
// it shall appear before the declaration of the module whose delay mode it
// controls. All three rules are carried by the preprocessor, which recognizes
// the directive, records the selected mode queried below, and rejects the
// directive when it appears inside a design element.

namespace {

// E7-C1/C2 (declarative + syntax): the bare directive is recognized before a
// module declaration and records the zero delay mode for what follows.
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

// E7-C1 (baseline): with no directive present, no delay mode is in effect.
TEST(Preprocessor, DelayModeZero_DefaultStateNoDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "module t;\nendmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kNone);
}

// E7-C3 (shall): the directive shall precede the module declaration; placing it
// inside a design element is illegal and is rejected.
TEST(Preprocessor, DelayModeZero_IllegalInsideModule) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module t;\n"
                           "`delay_mode_zero\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(f.diag.HasErrors());
}

// E7-C3 (shall, boundary): once a module declaration has closed, the design
// element nesting is back at the top level, so the directive is legal again
// before the next module and records the mode for the module that follows.
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

// E7-C1 (sequencing edge): the directive selects the zero delay mode for what
// follows it, so issuing it after a different mode directive supersedes that
// earlier mode. The recording stage ends with the zero mode in effect.
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

}  // namespace
