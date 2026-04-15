
#include "fixture_elaborator.h"

namespace {

// --- Valid: input port with default elaborates ---

TEST(DefaultPortValueElaboration, InputPortWithDefaultElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m(input logic a = 1'b0); endmodule"));
}

TEST(DefaultPortValueElaboration, MultipleInputPortsWithDefaultsElaborate) {
  EXPECT_TRUE(ElabOk(
      "module m(input logic a = 1'b0, input logic b = 1'b1); endmodule"));
}

TEST(DefaultPortValueElaboration, InputPortDefaultFromParameterElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m #(parameter P = 8'hFF)\n"
      "          (input logic [7:0] x = P);\n"
      "endmodule"));
}

TEST(DefaultPortValueElaboration, MixedPortsWithAndWithoutDefaultsElaborate) {
  EXPECT_TRUE(ElabOk(
      "module m(\n"
      "  input logic clk,\n"
      "  input logic rst = 1'b0,\n"
      "  output logic [7:0] data\n"
      ");\n"
      "endmodule"));
}

TEST(DefaultPortValueElaboration, LrmExampleBusConnElaborates) {
  EXPECT_TRUE(ElabOk(
      "module bus_conn (\n"
      "  output logic [7:0] dataout,\n"
      "  input        [7:0] datain = 8'hFF\n"
      ");\n"
      "  assign dataout = datain;\n"
      "endmodule"));
}

// --- Error: default on output port ---

TEST(DefaultPortValueElaboration, OutputPortWithDefaultIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(output logic q = 1'b0); endmodule", f, "m");
  EXPECT_TRUE(f.has_errors);
}

// --- Error: default on inout port ---

TEST(DefaultPortValueElaboration, InoutPortWithDefaultIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(inout logic x = 1'b0); endmodule", f, "m");
  EXPECT_TRUE(f.has_errors);
}

// --- Error: default on ref port ---

TEST(DefaultPortValueElaboration, RefPortWithDefaultIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(ref logic x = 1'b0); endmodule", f, "m");
  EXPECT_TRUE(f.has_errors);
}

// --- Error: default on non-ANSI port ---

TEST(DefaultPortValueElaboration, NonAnsiPortWithDefaultIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  input logic a = 1'b0;\n"
      "endmodule",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

// --- Error: default on interconnect port ---

TEST(DefaultPortValueElaboration, InterconnectPortWithDefaultIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input interconnect x = 1'b0); endmodule", f, "m");
  EXPECT_TRUE(f.has_errors);
}

// --- Error: default on non-singular (unpacked array) port ---

TEST(DefaultPortValueElaboration, NonSingularPortWithDefaultIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic x [3:0] = '{0, 0, 0, 0}); endmodule", f, "m");
  EXPECT_TRUE(f.has_errors);
}

// --- Instantiation: default value inserted for omitted input port ---

TEST(DefaultPortValueElaboration, OmittedInputUsesDefaultNamedConn) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, input logic [7:0] b = 8'hFF);\n"
      "  assign a = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- LRM example: default port scope resolution ---

TEST(DefaultPortValueElaboration, DefaultEvaluatedInModuleScope) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "parameter logic [7:0] My_DataIn = 8'hFF;\n"
      "module bus_conn (\n"
      "  output logic [7:0] dataout,\n"
      "  input        [7:0] datain = My_DataIn\n"
      ");\n"
      "  assign dataout = datain;\n"
      "endmodule\n"
      "module bus_connect1 (\n"
      "  output logic [31:0] dataout,\n"
      "  input        [ 7:0] datain\n"
      ");\n"
      "  parameter logic [7:0] My_DataIn = 8'h00;\n"
      "  bus_conn bconn1 (dataout[23:16]);\n"
      "endmodule\n",
      f, "bus_connect1");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
