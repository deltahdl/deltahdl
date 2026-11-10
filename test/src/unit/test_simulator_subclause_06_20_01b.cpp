#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ParameterPortKeywordSim,
     ClauseExampleInterfaceTypeParameterIsOverridable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef logic [7:0] word;\n"
                       "interface simple_bus #(AWIDTH = 64, type T = word)\n"
                       "    (input logic clk);\n"
                       "  T d;\n"
                       "endinterface\n"
                       "module top;\n"
                       "  logic clk;\n"
                       "  simple_bus #(.T(logic [15:0])) b(clk);\n"
                       "  simple_bus c(clk);\n"
                       "  initial $display(\"%0d %0d %0d\", $bits(b.d), "
                       "$bits(c.d), c.AWIDTH);\n"
                       "endmodule\n",
                       f),
            "16 8 64\n");
}

TEST(ParameterPortKeywordSim, ProgramParameterWithoutTheKeywordIsOverridable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p #(int W = 4);\n"
                       "  initial $display(\"%0d\", W);\n"
                       "endprogram\n"
                       "module top;\n"
                       "  p #(.W(8)) u();\n"
                       "endmodule\n",
                       f),
            "8\n");
}

TEST(NoDefaultParameterSim,
     DISABLED_DefparamSuppliesTheValueOfAParameterWithoutADefault) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child #(parameter int P);\n"
                       "  initial $display(\"%0d\", P);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child u0();\n"
                       "  defparam u0.P = 7;\n"
                       "endmodule\n",
                       f),
            "7\n");
}

TEST(NoDefaultParameterSim, InterfaceAndProgramReadTheirOverrides) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc #(parameter int P);\n"
                       "  initial $display(\"i %0d\", P);\n"
                       "endinterface\n"
                       "program prg #(parameter int P);\n"
                       "  initial $display(\"p %0d\", P);\n"
                       "endprogram\n"
                       "module top;\n"
                       "  ifc #(.P(3)) i();\n"
                       "  prg #(4) p();\n"
                       "endmodule\n",
                       f),
            "i 3\np 4\n");
}

TEST(BodyParameterLocalitySim,
     InterfaceAndProgramBodyParametersWithoutAPortListReadTheirOverrides) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  parameter int P = 1;\n"
                       "  initial $display(\"i %0d\", P);\n"
                       "endinterface\n"
                       "program prg;\n"
                       "  parameter int P = 1;\n"
                       "  initial $display(\"p %0d\", P);\n"
                       "endprogram\n"
                       "module top;\n"
                       "  ifc #(.P(5)) i();\n"
                       "  prg #(.P(6)) p();\n"
                       "endmodule\n",
                       f),
            "i 5\np 6\n");
}

TEST(BodyParameterLocalitySim, ClassSpecializationSetsAPortParameterOnly) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C #(int P = 1);\n"
                       "  parameter int Q = 2;\n"
                       "endclass\n"
                       "module top;\n"
                       "  C #(.P(3)) h;\n"
                       "  initial begin\n"
                       "    h = new;\n"
                       "    $display(\"%0d %0d\", h.P, h.Q);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3 2\n");
}

struct ClassPlace {
  std::string_view name;
  std::string_view before_class;
  std::string_view after_class;
  std::string_view prefix;
};

constexpr ClassPlace kClassPlaces[] = {
    {"compilation unit", "", "module top;\n", ""},
    {"package", "package q;\n", "endpackage\nmodule top;\n", "q::"},
    {"module", "module top;\n", "", ""},
    {"nested class", "class O;\n", "endclass\nmodule top;\n", "O::"},
};

std::string ClassRead(const ClassPlace& place, std::string_view display) {
  std::string body(display);
  for (size_t at = body.find('@'); at != std::string::npos;
       at = body.find('@', at)) {
    body.replace(at, 1, place.prefix);
    at += place.prefix.size();
  }
  return std::string(place.before_class) +
         "class C #(int W = 1);\n"
         "  parameter int P = 2;\n"
         "  parameter type T = int;\n"
         "  parameter int Q = W * 2;\n"
         "endclass\n" +
         std::string(place.after_class) + "  initial $display(" + body +
         ");\nendmodule\n";
}

TEST(BodyParameterLocalitySim,
     BodyValuesStandUnderEverySpecializationInEveryPlace) {
  for (const auto& place : kClassPlaces) {
    SCOPED_TRACE(place.name);
    SimFixture f;
    EXPECT_EQ(RunCapture(ClassRead(place,
                                   "\"%0d %0d %0d %0d\", @C#(4)::P, "
                                   "@C#(.W(4))::P, @C#(4)::Q, @C#()::Q"),
                         f),
              "2 2 8 2\n");
  }
}

TEST(BodyParameterLocalitySim,
     BodyTypeParameterStaysItsTypeUnderASpecialization) {
  for (const auto& place : kClassPlaces) {
    if (place.name == "package") continue;
    SCOPED_TRACE(place.name);
    SimFixture f;
    EXPECT_EQ(RunCapture(ClassRead(place, "\"%0d\", $bits(@C#(4)::T)"), f),
              "32\n");
  }
}

TEST(BodyParameterLocalitySim, ClassWithoutAPortListKeepsItsBodyValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class c;\n"
                       "  parameter int A = 2;\n"
                       "endclass\n"
                       "module top;\n"
                       "  initial $display(\"%0d\", c::A);\n"
                       "endmodule\n",
                       f),
            "2\n");
}

}  // namespace
