#include <gtest/gtest.h>

#include <cstdint>

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

void ExpectReportedAt(const char* src, const char* message, uint32_t line,
                      const char* subclause) {
  ElabFixture f;
  EXPECT_FALSE(ElabOk(src, f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, subclause));
}

constexpr const char* kNotOverridable =
    "'randomize' is a built-in method and cannot be overridden";
constexpr const char* kTimeControl =
    "time-controlling statement is not allowed inside a function";

TEST(BehaviorOfRandomizationMethods, RandomizeInADerivedClassIsError) {
  ExpectReportedAt(
      "class B; rand int x; endclass\n"
      "class D extends B;\n"
      "  function int randomize(); return 1; endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      kNotOverridable, 3, "18.6.3");
}

TEST(BehaviorOfRandomizationMethods, RandomizeInAPackageClassIsError) {
  ExpectReportedAt(
      "package p;\n"
      "  class C;\n"
      "    virtual function int randomize(); return 1; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      kNotOverridable, 3, "18.6.3");
}

TEST(BehaviorOfRandomizationMethods, RandomizeInAModuleClassIsError) {
  ExpectReportedAt(
      "module m;\n"
      "  class C;\n"
      "    function int randomize(); return 1; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      kNotOverridable, 3, "18.6.3");
}

TEST(BehaviorOfRandomizationMethods, RandomizeInAProgramClassIsError) {
  ExpectReportedAt(
      "program p;\n"
      "  class C;\n"
      "    function int randomize(); return 1; endfunction\n"
      "  endclass\n"
      "endprogram\n",
      kNotOverridable, 3, "18.6.3");
}

TEST(BehaviorOfRandomizationMethods, RandomizeInAnInterfaceClassIsError) {
  ExpectReportedAt(
      "interface class I;\n"
      "  pure virtual function int randomize();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      kNotOverridable, 2, "18.6.3");
}

TEST(BehaviorOfRandomizationMethods, ExternRandomizePrototypeIsError) {
  ExpectReportedAt(
      "class C;\n"
      "  rand int x;\n"
      "  extern function int randomize();\n"
      "endclass\n"
      "function int C::randomize(); return 1; endfunction\n"
      "module m;\n"
      "endmodule\n",
      kNotOverridable, 3, "18.6.3");
}

TEST(BehaviorOfRandomizationMethods, StaticRandomizeIsError) {
  ExpectReportedAt(
      "class C;\n"
      "  rand int x;\n"
      "  static function int randomize(); return 1; endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      kNotOverridable, 3, "18.6.3");
}

TEST(BehaviorOfRandomizationMethods, AMethodOfAnotherNameInEachPlaceOk) {
  EXPECT_TRUE(
      ElabOk("class B; rand int x; endclass\n"
             "class D extends B;\n"
             "  extern function int draw();\n"
             "  static function int pick(); return 1; endfunction\n"
             "endclass\n"
             "function int D::draw(); return randomize(); endfunction\n"
             "package p;\n"
             "  class C; virtual function int draw(); return 1; endfunction\n"
             "  endclass\n"
             "endpackage\n"
             "interface class I;\n"
             "  pure virtual function int draw();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(BehaviorOfRandomizationMethods, PostRandomizeWithEventControlCannotBlock) {
  ExpectReportedAt(
      "class C;\n"
      "  rand int x;\n"
      "  event e;\n"
      "  function void post_randomize(); @(e); endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      kTimeControl, 4, "13.4");
}

TEST(BehaviorOfRandomizationMethods, PreRandomizeWithWaitCannotBlock) {
  ExpectReportedAt(
      "class C;\n"
      "  rand int x;\n"
      "  function void pre_randomize(); wait (x > 0); endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      kTimeControl, 3, "13.4");
}

TEST(BehaviorOfRandomizationMethods, PostRandomizeWithWaitCannotBlock) {
  ExpectReportedAt(
      "class C;\n"
      "  rand int x;\n"
      "  function void post_randomize(); wait (x > 0); endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      kTimeControl, 3, "13.4");
}

TEST(BehaviorOfRandomizationMethods, ForkJoinInEitherHookCannotBlock) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  int y;\n"
             "  function void pre_randomize(); fork y = 1; join endfunction\n"
             "  function void post_randomize(); fork y = 2; join endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  for (uint32_t line : {4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "only fork/join_none is permitted inside a "
                              "function",
                              line, "13.4"))
        << line;
  }
}

TEST(BehaviorOfRandomizationMethods, ForkJoinNoneInEitherHookOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  int y;\n"
             "  function void pre_randomize(); fork y = 1; join_none "
             "endfunction\n"
             "  function void post_randomize(); fork y = 2; join_none "
             "endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(BehaviorOfRandomizationMethods,
     DISABLED_PreRandomizeEnablingATaskCannotBlock) {
  ExpectReportedAt(
      "class C;\n"
      "  rand int x;\n"
      "  task t(); #1; endtask\n"
      "  function void pre_randomize(); t(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      "function cannot enable a task", 4, "13.4");
}

TEST(BehaviorOfRandomizationMethods,
     DISABLED_PostRandomizeEnablingATaskCannotBlock) {
  ExpectReportedAt(
      "class C;\n"
      "  rand int x;\n"
      "  task t(); #1; endtask\n"
      "  function void post_randomize(); t(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      "function cannot enable a task", 4, "13.4");
}

TEST(BehaviorOfRandomizationMethods, HooksCallingAFunctionOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void f(); endfunction\n"
             "  function void pre_randomize(); f(); endfunction\n"
             "  function void post_randomize(); f(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
