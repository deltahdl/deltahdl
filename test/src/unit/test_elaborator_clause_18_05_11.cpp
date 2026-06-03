#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.5.11: a function called from a constraint may take input arguments. With
// only input formals the call is legal.
TEST(FunctionsInConstraints, InputArgumentFunctionAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a); return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: a function used in a constraint shall not have output arguments.
TEST(FunctionsInConstraints, OutputArgumentFunctionRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(output int a); a = 1; return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: a function used in a constraint shall not have inout arguments.
TEST(FunctionsInConstraints, InoutArgumentFunctionRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(inout int a); return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: a non-const ref argument is also forbidden in a constraint function,
// since the call could write back into a variable through the reference.
TEST(FunctionsInConstraints, NonConstRefArgumentFunctionRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(ref int a); return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: a const ref argument is expressly allowed, so a constraint function
// taking one is accepted.
TEST(FunctionsInConstraints, ConstRefArgumentFunctionAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(const ref int a); return a; endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: the restriction targets functions actually used in a constraint. A
// function with a ref argument that is never called from a constraint is fine.
TEST(FunctionsInConstraints, RefArgumentFunctionNotInConstraintAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function int f(ref int a); return a; endfunction\n"
             "  constraint c1 { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: a function used in a constraint cannot modify the constraints by
// calling rand_mode(). A constraint function whose body does so is rejected.
TEST(FunctionsInConstraints, ConstraintFunctionCallingRandModeRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a); this.rand_mode(0); return a; "
             "endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: likewise a constraint function shall not call constraint_mode().
TEST(FunctionsInConstraints, ConstraintFunctionCallingConstraintModeRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a); this.constraint_mode(0); return a; "
             "endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: a constraint function that calls neither built-in is fine, so an
// ordinary helper call in its body does not trip the no-modify rule.
TEST(FunctionsInConstraints, ConstraintFunctionWithBenignBodyAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int g(int a); return a + 1; endfunction\n"
             "  function int f(int a); return g(a); endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: the callee is resolved through the class hierarchy, so a function
// inherited from a base class is checked when a derived-class constraint calls
// it. A base function with an output argument is rejected from the derived
// constraint.
TEST(FunctionsInConstraints, BaseClassFunctionWithOutputArgRejected) {
  EXPECT_FALSE(
      ElabOk("class Base;\n"
             "  function int f(output int a); a = 0; return a; endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: the restriction applies to every formal, not just the first. A
// function whose offending argument follows a permitted one is still rejected,
// so the argument scan must look past the leading input argument.
TEST(FunctionsInConstraints, LaterArgumentBadDirectionRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a, output int b); b = 0; return a; "
             "endfunction\n"
             "  constraint c1 { x == f(y, x); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: a function with no arguments has nothing to forbid, so calling one in
// a constraint is legal — the empty argument list is the boundary of the scan.
TEST(FunctionsInConstraints, NoArgumentFunctionAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  function int f(); return 7; endfunction\n"
             "  constraint c1 { x == f(); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: the no-modify rule reaches a rand_mode()/constraint_mode() call buried
// inside the function body, not just one at the top level. A call nested in a
// control-flow statement is found by the recursive body scan and rejected.
TEST(FunctionsInConstraints, ModeMethodCallNestedInControlFlowRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int f(int a);\n"
             "    if (a > 0) this.rand_mode(0);\n"
             "    return a;\n"
             "  endfunction\n"
             "  constraint c1 { x == f(y); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// 18.5.11: the restrictions apply to every function called in the constraint,
// including one nested as the argument of another call. An inner function with a
// forbidden output argument is rejected even though the outer call is benign.
TEST(FunctionsInConstraints, NestedConstraintCallInnerFunctionChecked) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  rand int y;\n"
             "  function int inner(output int a); a = 0; return a; endfunction\n"
             "  function int outer(int a); return a; endfunction\n"
             "  constraint c1 { x == outer(inner(y)); }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
