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

TEST(WildcardConnectionRun, AnInterfacePortTakesTheLikeNamedInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface bus;\n  logic r;\nendinterface\n"
                       "module c(bus b);\n"
                       "  initial #1 $display(\"%b\", b.r);\n"
                       "endmodule\n"
                       "module t;\n  bus b();\n  initial b.r = 1;\n"
                       "  c u(.*);\nendmodule\n",
                       f),
            "1\n");
}

TEST(WildcardConnectionRun, AMissingSignalLeavesTheDefaultInPlace) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module c(input a = 1);\n"
                       "  initial #1 $display(\"%b\", a);\n"
                       "endmodule\n"
                       "module t;\n  c u(.*);\nendmodule\n",
                       f),
            "1\n");
}

std::string WildcardImportRun(const std::string& connections, SimFixture& f) {
  return RunCapture(
      "package p;\n  logic wc = 1;\n  logic wd = 1;\nendpackage\n"
      "module child(input wc, wd);\n"
      "  initial #1 $display(\"%b %b\", wc, wd);\n"
      "endmodule\n"
      "module t;\n  import p::*;\n  child u0(" +
          connections + ");\nendmodule\n",
      f);
}

TEST(WildcardConnectionRun, AWildcardAloneImportsNoName) {
  SimFixture f;
  EXPECT_EQ(WildcardImportRun(".*", f), "z z\n");
}

TEST(WildcardConnectionRun, AnImplicitNamedConnectionBesideItImportsTheName) {
  SimFixture f;
  EXPECT_EQ(WildcardImportRun(".*, .wc", f), "1 z\n");
}

TEST(WildcardConnectionRun, DISABLED_ANamedConnectionBesideItImportsTheName) {
  SimFixture f;
  EXPECT_EQ(WildcardImportRun(".*, .wd(wd)", f), "z 1\n");
}

}  // namespace
