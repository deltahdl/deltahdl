#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PrePostRandomizePrototype, ConformingOverridesOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void pre_randomize(); endfunction\n"
             "  function void post_randomize(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(PrePostRandomizePrototype, NonVoidPreRandomizeError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function int pre_randomize(); return 0; endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'pre_randomize' shall have a void return type", 2,
                            "18.6.2"));
}

TEST(PrePostRandomizePrototype, NonVoidPostRandomizeError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function int post_randomize(); return 0; endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'post_randomize' shall have a void return type", 2,
                            "18.6.2"));
}

TEST(PrePostRandomizePrototype, PreRandomizeWithArgError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function void pre_randomize(int a); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'pre_randomize' shall take no arguments", 2,
                            "18.6.2"));
}

TEST(PrePostRandomizePrototype, PostRandomizeWithArgError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function void post_randomize(int a); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'post_randomize' shall take no arguments", 2,
                            "18.6.2"));
}

TEST(PrePostRandomizePrototype, PreRandomizeTaskFormError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  task pre_randomize(); endtask\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'pre_randomize' shall be a void function taking "
                            "no arguments, not a task",
                            2, "18.6.2"));
}

TEST(PrePostRandomizePrototype, PostRandomizeTaskFormError) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  task post_randomize(); endtask\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'post_randomize' shall be a void function taking "
                            "no arguments, not a task",
                            2, "18.6.2"));
}

}  // namespace
