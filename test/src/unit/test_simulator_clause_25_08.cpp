#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ParameterizedInterfaceSim, OverrideWidthHoldsAssignedValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(.WIDTH(16)) u0();\n"
      "  initial u0.data = 16'hAB;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"u0.data", 0xABu}});
}

TEST(ParameterizedInterfaceSim, DefaultWidthHoldsAssignedValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc u0();\n"
      "  initial u0.data = 8'h5A;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"u0.data", 0x5Au}});
}

TEST(ParameterizedInterfaceSim, IndependentInstancesHoldIndependentValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(.WIDTH(4)) a();\n"
      "  ifc #(.WIDTH(16)) b();\n"
      "  initial begin\n"
      "    a.data = 4'hC;\n"
      "    b.data = 16'h0123;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a.data", 0xCu}, {"b.data", 0x0123u}});
}

}  // namespace
