#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.23 — type(this) represents the type of the enclosing class. Inside a
// method of class C, comparing type(this) against type(C) matches, so the
// method takes the true branch. The class and the call are built from real
// source syntax and driven through the full pipeline; the returned value is
// observed at run time.
TEST(TypeOfThisSim, MatchesEnclosingClass) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  function int check();\n"
                      "    int r;\n"
                      "    if (type(this) == type(C)) r = 1;\n"
                      "    else r = 2;\n"
                      "    return r;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.check();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.23 — type(this) is the enclosing class, so it does not match a different
// class. Comparing type(this) in C against type(D) is false; the else branch
// runs.
TEST(TypeOfThisSim, DiffersFromOtherClass) {
  EXPECT_EQ(RunAndGet("class D;\n"
                      "endclass\n"
                      "class C;\n"
                      "  function int check();\n"
                      "    int r;\n"
                      "    if (type(this) == type(D)) r = 1;\n"
                      "    else r = 2;\n"
                      "    return r;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.check();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            2u);
}

// §6.23 — a class type reference never matches a built-in type reference, so
// type(this) compared against type(int) is false.
TEST(TypeOfThisSim, DiffersFromBuiltinType) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  function int check();\n"
                      "    int r;\n"
                      "    if (type(this) == type(int)) r = 1;\n"
                      "    else r = 2;\n"
                      "    return r;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.check();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            2u);
}

// §6.23 — the inequality form negates the match, so type(this) != type(int) is
// true inside a class method.
TEST(TypeOfThisSim, InequalityWithBuiltinIsTrue) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  function int check();\n"
                      "    int r;\n"
                      "    if (type(this) != type(int)) r = 1;\n"
                      "    else r = 2;\n"
                      "    return r;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.check();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.23/§8.11 — type(this) resolves to the enclosing class even in a static
// method, where there is no instance handle: the class is the one whose method
// body is executing. A static check() compares type(this) against type(C) and
// matches.
TEST(TypeOfThisSim, MatchesEnclosingClassInStaticMethod) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static function int check();\n"
                      "    int r;\n"
                      "    if (type(this) == type(C)) r = 1;\n"
                      "    else r = 2;\n"
                      "    return r;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = C::check();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

}  // namespace
