#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §13.7/§23.8.1: Forward reference to function declared later in same module.
TEST(Elab1370, ForwardFunctionReference) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial x = add(1, 2);\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.7/§23.8.1: Forward reference to task declared later in same module.
TEST(Elab1370, ForwardTaskReference) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial set_x();\n"
      "  task set_x;\n"
      "    x = 8'd42;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.7: Task calling a function defined after it (both forward references).
TEST(Elab1370, TaskCallsForwardFunction) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  task do_work;\n"
      "    x = compute(5);\n"
      "  endtask\n"
      "  function int compute(int v);\n"
      "    return v * 2;\n"
      "  endfunction\n"
      "  initial do_work();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.7: Mutually recursive functions (both declared in same module).
TEST(Elab1370, MutuallyRecursiveFunctions) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int is_even(int n);\n"
      "    if (n == 0) return 1;\n"
      "    return is_odd(n - 1);\n"
      "  endfunction\n"
      "  function int is_odd(int n);\n"
      "    if (n == 0) return 0;\n"
      "    return is_even(n - 1);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
