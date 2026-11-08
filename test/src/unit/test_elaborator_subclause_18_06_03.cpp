#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(BehaviorOfRandomizationMethods, RandomizeOverrideIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function int randomize(); return 1; endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'randomize' is a built-in method and cannot be overridden",
                    3, "18.6.3"));
}

TEST(BehaviorOfRandomizationMethods, NoRandomizeOverrideOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(BehaviorOfRandomizationMethods, PreRandomizeCannotBlock) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void pre_randomize(); #5; endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 3,
      "13.4"));
}

TEST(BehaviorOfRandomizationMethods, PostRandomizeCannotBlock) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void post_randomize(); #5; endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 3,
      "13.4"));
}

TEST(BehaviorOfRandomizationMethods, NonBlockingPrePostRandomizeOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  int seen;\n"
             "  function void pre_randomize(); seen = 1; endfunction\n"
             "  function void post_randomize(); seen = 2; endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(BehaviorOfRandomizationMethods, RandomizeVoidOverrideIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void randomize(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'randomize' is a built-in method and cannot be overridden",
                    3, "18.6.3"));
}

TEST(BehaviorOfRandomizationMethods, RandomizeTaskOverrideIsError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  task randomize(); endtask\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'randomize' is a built-in method and cannot be overridden",
                    3, "18.6.3"));
}

TEST(BehaviorOfRandomizationMethods, PreRandomizeWithEventControlCannotBlock) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  event e;\n"
             "  function void pre_randomize(); @(e); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 4,
      "13.4"));
}

}  // namespace
