#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PortDeclSim, VariablePortTypeInputAndOutputCarryValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  child u(8'd42, result);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 42u}});
}

TEST(PortDeclSim, NetPortTypeInputCarriesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  child u(8'd55, result);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 55u}});
}

TEST(PortDeclSim, OutputPortDrivesValueOutward) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output logic [7:0] q);\n"
      "  assign q = 8'd123;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  child u(result);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 123u}});
}

TEST(PortDeclSim, PortIdentifierListYieldsIndependentPorts) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, b,\n"
      "             output logic [7:0] x, output logic [7:0] y);\n"
      "  assign x = a;\n"
      "  assign y = b;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] rx, ry;\n"
      "  child u(8'd7, 8'd9, rx, ry);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"rx", 7u}, {"ry", 9u}});
}

TEST(PortDeclSim, BodyPortsOfAPackageScopedTypeCarryItsWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  typedef logic [3:0] nib_t;\n"
      "endpackage\n"
      "module child(a, b);\n"
      "  input pk::nib_t a;\n"
      "  output pk::nib_t b;\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [3:0] result;\n"
      "  logic [3:0] passed;\n"
      "  function automatic logic [3:0] pass;\n"
      "    input pk::nib_t x;\n"
      "    pass = x;\n"
      "  endfunction\n"
      "  child u(4'hA, result);\n"
      "  initial passed = pass(4'hA);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 0xAu}, {"passed", 0xAu}});
}

TEST(PortDeclSim, VarPortsOfATypeReferenceCarryTheReferencedType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m(input var int x, input var type(x) a,\n"
      "         output var type(x) b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module n(c, d);\n"
      "  int x;\n"
      "  input var type(x) c;\n"
      "  output var type(x) d;\n"
      "  assign d = c;\n"
      "endmodule\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  m u1(0, -5, r1);\n"
      "  n u2(-5, r2);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 0xFFFFFFFBu}, {"r2", 0xFFFFFFFBu}});
}

}  // namespace
