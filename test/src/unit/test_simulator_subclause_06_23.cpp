#include <gtest/gtest.h>

#include <string>

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

// §6.23 with A.2.8: `var type(a) v;` among a block's items declares v with the
// self-determined type of `a`, so v is the 32-bit signed int of `int a` and
// holds -7, which a one-bit v would read as 1.
TEST(TypeOfExprBlockVarSim, TakesTheIntTypeOfAModuleVariable) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int a = 3;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    var automatic type(a) v = -7;\n"
                      "    r = v;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xFFFFFFF9u);
}

// §6.23: the type of `w`, `logic [11:0]`, gives x twelve bits, so all twelve
// written ones survive and $bits(x) is 12.
TEST(TypeOfExprBlockVarSim, TakesTheVectorTypeOfAModuleVariable) {
  const std::string kSrc =
      "module t;\n"
      "  logic [11:0] w;\n"
      "  int r, b;\n"
      "  initial begin\n"
      "    var type(w) x;\n"
      "    x = 12'hFFF;\n"
      "    r = x;\n"
      "    b = $bits(x);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 4095u);
  EXPECT_EQ(RunAndGet(kSrc, "b"), 12u);
}

// §6.23 takes the type of the expression with the names in scope at the
// declaration, so the block's own `shortint a` hides the module's 4-bit `a`:
// z is 16 bits wide and signed, and holds -2.
TEST(TypeOfExprBlockVarSim, TakesTheTypeOfAnEarlierBlockLocal) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] a;\n"
      "  int r, b;\n"
      "  initial begin\n"
      "    shortint a;\n"
      "    var automatic type(a) z = -2;\n"
      "    r = z;\n"
      "    b = $bits(z);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0xFFFFFFFEu);
  EXPECT_EQ(RunAndGet(kSrc, "b"), 16u);
}

}  // namespace
