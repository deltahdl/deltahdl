#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kUnit =
    "parameter shortreal US = 0.1;\n"
    "parameter real UR = 0.25;\n"
    "package p;\n"
    "  parameter real S = 0.1;\n"
    "  parameter shortreal SS = 0.5;\n"
    "endpackage\n"
    "package q;\n"
    "  import p::*;\n"
    "  parameter real Q = S * 2;\n"
    "  parameter shortreal Q2 = p::SS + 1.0;\n"
    "endpackage\n"
    "import p::SS;\n"
    "localparam real UL = US * 2;\n"
    "localparam bit UEQ = (US == 0.1);\n";

constexpr const char* kReads =
    "  localparam real PD = p::S;\n"
    "  localparam bit PEQ = (p::S == 0.1);\n"
    "  localparam bit PGT = (p::S > 0.05);\n"
    "  localparam real UD = US;\n"
    "  localparam bit UNE = (US == 0.1);\n"
    "  localparam real ID = SS * 2;\n"
    "  localparam real QD = q::Q;\n"
    "  localparam real Q2D = q::Q2;\n"
    "  localparam real RD = $unit::UR;\n";

std::string Show(const std::string& scope) {
  return "$display(\"%.2f %0d %0d %.9f %0d %.2f %.2f %.2f %.2f\", " + scope +
         "PD, " + scope + "PEQ, " + scope + "PGT, " + scope + "UD, " + scope +
         "UNE, " + scope + "ID, " + scope + "QD, " + scope + "Q2D, " + scope +
         "RD);\n";
}

std::string Placed(const std::string& place) {
  const std::string kTop =
      "  initial #1 $display(\"%.9f %0d\", UL, UEQ);\n"
      "endmodule\n";
  if (place == "class") {
    return std::string(kUnit) + "class C;\n" + kReads +
           "endclass\n"
           "module top;\n"
           "  initial " +
           Show("C::") + kTop;
  }
  if (place == "generate") {
    return std::string(kUnit) +
           "module top;\n"
           "  if (1) begin : g\n" +
           kReads + "    initial " + Show("") + "  end\n" + kTop;
  }
  return std::string(kUnit) + place + " m;\n" + kReads + "  initial " +
         Show("") + "end" + place +
         "\n"
         "module top;\n"
         "  m u();\n" +
         kTop;
}

TEST(LocalparamSimulation, RealPackageAndUnitParametersAreConstants) {
  for (const char* place :
       {"module", "interface", "program", "generate", "class"}) {
    SCOPED_TRACE(place);
    SimFixture f;
    EXPECT_EQ(RunCapture(Placed(place), f),
              "0.10 1 1 0.100000001 0 1.00 0.20 1.50 0.25\n"
              "0.200000003 0\n");
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

}  // namespace
