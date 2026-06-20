#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PassByValueSim, DefaultMechanismWithoutDirectionQualifier) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  function int add_ten(int v);\n"
      "    v = v + 10;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 5;\n"
      "    y = add_ten(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 5u}, {"y", 15u}});
}

TEST(PassByValueSim, AutomaticFunctionRetainsLocalCopy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  function automatic int modify_arg(input int v);\n"
      "    v = v + 100;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    y = modify_arg(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}, {"y", 107u}});
}

TEST(PassByValueSim, TaskInputArgNotVisibleOutside) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  task modify(input int v);\n"
      "    v = v + 100;\n"
      "    y = v;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    modify(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}, {"y", 107u}});
}

TEST(PassByValueSim, MultipleArgsCopiedIndependently) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  function int swap_and_add(int x, int y);\n"
      "    int tmp;\n"
      "    tmp = x;\n"
      "    x = y;\n"
      "    y = tmp;\n"
      "    return x + y;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a = 3;\n"
      "    b = 7;\n"
      "    result = swap_and_add(a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 3u}, {"b", 7u}, {"result", 10u}});
}

TEST(PassByValueSim, RecursiveAutomaticUsesPerActivationStackCopy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  function automatic int sum_down(int n);\n"
      "    if (n == 0) return 0;\n"
      "    return n + sum_down(n - 1);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = sum_down(4);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 10u}});
}

TEST(PassByValueSim, SameSourceBoundToTwoFormalsCopiesIndependently) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, result;\n"
      "  function int scale_first_minus_second(int a, int b);\n"
      "    a = a * 10;\n"
      "    return a - b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    result = scale_first_minus_second(x, x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}, {"result", 63u}});
}

}  // namespace
