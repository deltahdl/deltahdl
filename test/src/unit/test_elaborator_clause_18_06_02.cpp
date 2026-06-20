

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.6.2: a class may declare pre_randomize()/post_randomize() so long as the
// declaration matches the built-in prototype 'function void <name>();' — a
// void-returning function taking no arguments.
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

// 18.6.2: the prototype has a void return type; a value-returning override
// does not conform.
TEST(PrePostRandomizePrototype, NonVoidPreRandomizeError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function int pre_randomize(); return 0; endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(PrePostRandomizePrototype, NonVoidPostRandomizeError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function int post_randomize(); return 0; endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.6.2: the prototype takes no arguments; an override with a formal does not
// conform.
TEST(PrePostRandomizePrototype, PreRandomizeWithArgError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function void pre_randomize(int a); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(PrePostRandomizePrototype, PostRandomizeWithArgError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  function void post_randomize(int a); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.6.2: the prototype is a function; a task named pre_randomize does not
// conform.
TEST(PrePostRandomizePrototype, PreRandomizeTaskFormError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  task pre_randomize(); endtask\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.6.2: likewise a task named post_randomize does not conform to the
// 'function void post_randomize();' prototype.
TEST(PrePostRandomizePrototype, PostRandomizeTaskFormError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  task post_randomize(); endtask\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
