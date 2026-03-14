#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TaskFunctionNameSim, ForwardFunctionCallSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = double_it(8'd21);\n"
      "  function logic [7:0] double_it(input logic [7:0] v);\n"
      "    return v * 8'd2;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

TEST(TaskFunctionNameSim, ForwardTaskCallSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    set_val();\n"
      "  end\n"
      "  task set_val;\n"
      "    x = 8'd99;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 99u}});
}

TEST(TaskFunctionNameSim, FunctionCallsForwardFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] outer(input logic [7:0] v);\n"
      "    return inner(v) + 8'd1;\n"
      "  endfunction\n"
      "  function logic [7:0] inner(input logic [7:0] v);\n"
      "    return v * 8'd3;\n"
      "  endfunction\n"
      "  initial x = outer(8'd10);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 31u}});
}

}  // namespace
