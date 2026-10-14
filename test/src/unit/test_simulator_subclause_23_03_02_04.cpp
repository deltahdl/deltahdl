
#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(WildcardPortConnectionSimulation, WildcardInputPropagatesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = 8'hAB;\n"
      "  child u0(.*);\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(WildcardPortConnectionSimulation, NamedOverrideTakesPrecedence) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, input logic [7:0] b,\n"
      "             output logic [7:0] c);\n"
      "  assign c = a + b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b, c;\n"
      "  assign a = 8'd10;\n"
      "  assign b = 8'd20;\n"
      "  child u0(.a(8'd99), .*);\n"
      "endmodule\n",
      f, "c");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 119u);
}

TEST(WildcardPortConnectionSimulation, DefaultValueUsedForMissingSignal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, input logic [7:0] b = 8'hFF,\n"
      "             output logic [7:0] c);\n"
      "  assign c = a + b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, c;\n"
      "  assign a = 8'd1;\n"
      "  child u0(.*);\n"
      "endmodule\n",
      f, "c");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(WildcardPortConnectionSimulation,
     WildcardMixedWithImplicitNamePropagates) {
  // §23.3.2.4: a .* connection mixes with an implicit .name connection
  // (§23.3.2.3). The `.a` implicit named connection is built from real source
  // syntax; the .* then supplies the remaining ports. Both sides must reach the
  // child for the sum to appear, observed by running the design end to end.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, input logic [7:0] b,\n"
      "             output logic [7:0] c);\n"
      "  assign c = a + b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b, c;\n"
      "  assign a = 8'd3;\n"
      "  assign b = 8'd4;\n"
      "  child u0(.a, .*);\n"
      "endmodule\n",
      f, "c");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// §23.3.2.4: `.*` connects each port whose name exists in the instantiating
// scope, a variable an explicit import brings in among them, while a name only
// a wildcard import could supply is no sufficient reference and the port takes
// its default.
TEST(WildcardPortConnectionSimulation,
     ExplicitImportIsConnectedAndWildcardIsNot) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  logic [7:0] sig = 8'h5A;\n"
                       "  logic [7:0] wc = 8'h77;\n"
                       "endpackage\n"
                       "module child(input logic [7:0] sig = 8'h11,\n"
                       "             input logic [7:0] wc = 8'h22);\n"
                       "  initial #1 $display(\"%h %h\", sig, wc);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  import p::sig;\n"
                       "  import p::*;\n"
                       "  child u0(.*);\n"
                       "endmodule\n",
                       f),
            "5a 22\n");
}

}  // namespace
