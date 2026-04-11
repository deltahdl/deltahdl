#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PassByValueSim, PassByValueIsolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  function logic [7:0] modify_local(input logic [7:0] v);\n"
      "    v = v + 8'd10;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = modify_local(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 5u}, {"y", 15u}});
}

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

}  // namespace
