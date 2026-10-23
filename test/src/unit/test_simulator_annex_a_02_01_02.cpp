#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

// §A.2.1.2 end-to-end coverage. The port-declaration productions
// (inout/input/output/ref _declaration and interface_port_declaration) are
// pure syntax whose observable runtime consequence is that the DIRECTION named
// in each production actually governs how a value crosses the module boundary:
// an input carries a value inward, an output carries a value outward, and each
// admitted port type (net_port_type vs variable_port_type from §A.2.2.1) and
// each identifier in a list_of_port_identifiers (§A.2.3) becomes an independent
// port at runtime. The parser and elaborator files observe the productions
// being parsed and carried; these tests instead build each port from the real
// dependency syntax, instantiate the module, drive it, and run the design so
// the direction is observed actually moving the value.

namespace {

// input_declaration / output_declaration, variable_port_type (§A.2.2.1) form.
// The input carries the connected literal into the child; the output carries
// the copied value back out to the parent signal read after the run.
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

// input_declaration, net_port_type (§A.2.2.1) form: the input is declared with
// an explicit net type (`wire`) rather than a variable type. The value must
// still cross the boundary inward, confirming the net alternative of the
// production is wired at runtime just as the variable alternative is.
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

// output_declaration in isolation: the child drives its output from an internal
// constant with no input involved, so the observed parent value can only have
// arrived through the output direction moving the value outward.
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

// list_of_port_identifiers (§A.2.3): a single input_declaration names two
// identifiers in one comma list. At runtime that one declaration must yield two
// independent input ports, each carrying its own connected value. Reading the
// two distinct parent results shows the list produced separate ports rather
// than collapsing them.
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

// A body port declaration and a function's body port declaration (A.2.7) take
// a data_type, which A.2.2.1 lets name a package's typedef through its scope.
// Each port is then pk::nib_t's four bits, so 4'hA crosses whole; a one-bit
// port would carry its low bit, 0.
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

}  // namespace
