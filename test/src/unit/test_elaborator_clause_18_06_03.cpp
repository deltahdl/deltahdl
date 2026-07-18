#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.6.3: the randomize() method is built-in and cannot be overridden. A class
// that declares its own method named randomize is therefore an error, whatever
// the form of the declaration.
TEST(BehaviorOfRandomizationMethods, RandomizeOverrideIsError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function int randomize(); return 1; endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.6.3: the prohibition is on declaring randomize itself; a class with no
// such declaration uses the built-in method and elaborates without complaint,
// even when it declares random variables and constraints.
TEST(BehaviorOfRandomizationMethods, NoRandomizeOverrideOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.6.3: pre_randomize() and post_randomize() are functions and cannot block.
// A time-controlling statement in pre_randomize() makes it block, which is not
// permitted in a function and is reported as an error.
TEST(BehaviorOfRandomizationMethods, PreRandomizeCannotBlock) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void pre_randomize(); #5; endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.6.3: the same holds for post_randomize(): a delay inside it is a blocking
// statement that a function may not contain.
TEST(BehaviorOfRandomizationMethods, PostRandomizeCannotBlock) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void post_randomize(); #5; endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.6.3: a non-blocking pre_randomize()/post_randomize() — one whose body has
// no time-controlling statement — is the legal case the rule allows.
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

// 18.6.3 (edge of B4): the prohibition is on the name randomize, independent of
// the declared signature. A void-returning, argument-less override — the form
// that most resembles a legal method — is still rejected because randomize() is
// built-in and cannot be overridden.
TEST(BehaviorOfRandomizationMethods, RandomizeVoidOverrideIsError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function void randomize(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.6.3 (edge of B4, task syntactic position): the prohibition is on declaring
// the name randomize as a class method at all, whichever subroutine form is
// used. A member declared as a task named randomize takes a different parse
// than a function, but it is still an attempt to override the built-in method
// and is rejected the same way.
TEST(BehaviorOfRandomizationMethods, RandomizeTaskOverrideIsError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  task randomize(); endtask\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.6.3 (edge of B6): "cannot block" covers every time-controlling statement,
// not just a delay. An event-control wait inside pre_randomize() is likewise a
// blocking statement a function may not contain, and is rejected.
TEST(BehaviorOfRandomizationMethods, PreRandomizeWithEventControlCannotBlock) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  event e;\n"
             "  function void pre_randomize(); @(e); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
