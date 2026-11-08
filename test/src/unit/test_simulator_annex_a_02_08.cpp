#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(BlockItemDeclSim, DataDeclBlockItemProducesRuntimeValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    int tmp;\n"
      "    tmp = 8'd40;\n"
      "    x = tmp + 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

TEST(BlockItemDeclSim, LocalparamBlockItemProducesRuntimeValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    localparam int W = 8;\n"
      "    x = W;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 8u}});
}

TEST(BlockItemDeclSim, ParameterBlockItemProducesRuntimeValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    parameter int D = 4;\n"
      "    x = D;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 4u}});
}

TEST(BlockItemDeclSim, NettypeBlockItemLeavesTheStatementsAfterItRunning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] y;\n"
      "  task automatic tk(output logic [7:0] o);\n"
      "    nettype real rt;\n"
      "    o = 8'd5;\n"
      "  endtask\n"
      "  function int f;\n"
      "    nettype bit nb;\n"
      "    return 7;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    nettype logic [3:0] nt;\n"
      "    tk(x);\n"
      "    y = f() + 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 5u}, {"y", 37u}});
}

}  // namespace
