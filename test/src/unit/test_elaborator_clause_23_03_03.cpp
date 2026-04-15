
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- R1/R4: Both sides of a port connection shall have assignment-compatible
//     data types (§6.22.3 rules) ---

TEST(PortConnectionRulesElaboration, CompatibleIntegralTypesAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a, output logic [7:0] b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  bit [7:0] x;\n"
             "  logic [7:0] y;\n"
             "  child u(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesElaboration, DifferentWidthIntegralsAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a, output logic [7:0] b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  logic [3:0] x;\n"
             "  logic [7:0] y;\n"
             "  child u(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesElaboration, RealToIntegralPortAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input integer a, output integer b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  real x;\n"
             "  integer y;\n"
             "  child u(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesElaboration, IncompatibleTypesOnPortConnectionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input logic [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  string s;\n"
      "  child u(.a(s));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// --- R5: User-defined nettype matching on port connections ---

TEST(PortConnectionRulesElaboration, NettypeSignalOnInputPortAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a);\n"
             "endmodule\n"
             "module top;\n"
             "  nettype logic [7:0] mytype;\n"
             "  mytype x;\n"
             "  child u(.a(x));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesElaboration, NettypeSignalOnOutputPortAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input logic [7:0] a, output logic [7:0] b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  nettype logic [7:0] mytype;\n"
             "  logic [7:0] x;\n"
             "  mytype y;\n"
             "  child u(.a(x), .b(y));\n"
             "endmodule\n"));
}

TEST(PortConnectionRulesElaboration, NettypeSignalOnInoutPortErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout wire [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  nettype logic [7:0] mytype;\n"
      "  mytype x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
