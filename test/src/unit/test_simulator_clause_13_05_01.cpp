#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SubroutineCallBasicSim, PassByValueIsolation) {
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

TEST(SubroutineCallBasicSim, InoutCopyInOut) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void inc(inout logic [7:0] v);\n"
      "    v = v + 8'd1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    inc(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 11u}});
}

}  // namespace
