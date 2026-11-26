#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr std::string_view kChildren =
    "module m #(type T = int) (); T x; endmodule\n"
    "interface i #(type T = int) (); T x; endinterface\n"
    "program p #(type T = int) (); T x; endprogram\n";

std::string Printed(std::string_view design) {
  std::string text(kChildren);
  text.append(design);
  SCOPED_TRACE(text);
  SimFixture f;
  return RunCapture(text, f);
}

TEST(OverrideEnumerationSim, ModuleInstanceDeclaresItsConstantsInItsParent) {
  EXPECT_EQ(Printed("module top;\n"
                    "  m #(enum {A, B}) u();\n"
                    "  m #(.T(enum {C, D = 5})) v1(), v2();\n"
                    "  int y = B;\n"
                    "  initial $display(\"%0d %0d\", y, D);\n"
                    "endmodule\n"),
            "1 5\n");
}

TEST(OverrideEnumerationSim, InterfaceAndProgramInstancesDeclareTheirs) {
  EXPECT_EQ(Printed("module top;\n"
                    "  i #(enum logic [1:0] {E = 2, F}) w();\n"
                    "  p #(.T(enum {G = 7, H})) z();\n"
                    "  initial $display(\"%0d %0d %0d\", F, H, $bits(w.x));\n"
                    "endmodule\n"),
            "3 8 2\n");
}

TEST(OverrideEnumerationSim, InstanceInAnInterfaceDeclaresInTheInterface) {
  EXPECT_EQ(Printed("interface j;\n"
                    "  i #(enum {A, B = 4}) w();\n"
                    "  int y = B;\n"
                    "endinterface\n"
                    "module top;\n"
                    "  j k();\n"
                    "  initial #1 $display(\"%0d\", k.y);\n"
                    "endmodule\n"),
            "4\n");
}

TEST(OverrideEnumerationSim, InstanceInAGenerateBlockDeclaresInTheBlock) {
  EXPECT_EQ(Printed("module top;\n"
                    "  if (1) begin : g\n"
                    "    m #(enum {A, B = 6}) u();\n"
                    "    initial $display(\"%0d\", B);\n"
                    "  end\n"
                    "  for (genvar n = 0; n < 2; n++) begin : l\n"
                    "    m #(.T(enum {C = 8, D})) u();\n"
                    "    initial #1 $display(\"%0d\", D + n);\n"
                    "  end\n"
                    "endmodule\n"),
            "6\n9\n10\n");
}

struct Place {
  std::string_view open;
  std::string_view close;
};

constexpr Place kDeclarationPlaces[] = {
    {"module top;\n", "endmodule\n"},
    {"interface j;\n", "endinterface\nmodule top; j u(); endmodule\n"},
    {"program q;\n", "endprogram\nmodule top; q u(); endmodule\n"},
    {"module top;\nif (1) begin : g\n", "end\nendmodule\n"},
    {"module top;\nfor (genvar n = 0; n < 1; n++) begin : l\n",
     "end\nendmodule\n"},
};

TEST(SpecializationEnumerationSim, ArgumentDeclaresItsConstantsInEachPlace) {
  for (const Place& place : kDeclarationPlaces) {
    std::string design = "class X #(type T = int); T v; endclass\n";
    design.append(place.open)
        .append(
            "  X #(enum {A, B}) k = new;\n"
            "  X #(.T(enum {C, D = 5})) h = new, g = new;\n"
            "  typedef X #(enum logic [1:0] {E = 2, F}) x_t;\n"
            "  x_t s = new;\n"
            "  x_t r = new;\n"
            "  initial begin\n"
            "    k.v = B;\n"
            "    $display(\"%0d %0d %0d %0d\", k.v, D, F, $bits(s.v));\n"
            "  end\n")
        .append(place.close);
    EXPECT_EQ(Printed(design), "1 5 3 2\n");
  }
}

TEST(InitializerOperandEnumerationSim, OperandDeclaresItsConstantsInEachPlace) {
  for (const Place& place : kDeclarationPlaces) {
    std::string design(place.open);
    design
        .append(
            "  int w = $bits(enum {A, B}), v = $bits(enum {C, D = 5});\n"
            "  int y = B;\n"
            "  int u = $bits(type(enum logic [1:0] {E = 2, F}));\n"
            "  localparam int P = $bits(enum {G, H = 7});\n"
            "  wire integer z = $bits(enum {I = 3, J});\n"
            "  initial #1 $display(\"%0d %0d %0d %0d %0d %0d %0d %0d %0d\",\n"
            "                      w, y, v, D, u, F, P + H, z, J);\n")
        .append(place.close);
    EXPECT_EQ(Printed(design), "32 1 32 5 2 3 39 32 4\n");
  }
}

TEST(TypeReferenceEnumerationSim, DeclarationDeclaresItsConstantsInEachPlace) {
  for (const Place& place : kDeclarationPlaces) {
    std::string design(place.open);
    design
        .append(
            "  var type(enum {A, B}) e = B, g;\n"
            "  var type(enum logic [1:0] {C = 2, D}) f;\n"
            "  initial #1 $display(\"%0d %0d %0d %0d %0d\",\n"
            "                      e, $bits(e), $bits(f), D, g);\n")
        .append(place.close);
    EXPECT_EQ(Printed(design), "1 32 2 3 0\n");
  }
}

TEST(StatementOperandEnumerationSim, OperandDeclaresItsConstantsInEachPlace) {
  for (const Place& place : kDeclarationPlaces) {
    std::string design(place.open);
    design
        .append(
            "  int w, k, v, u;\n"
            "  assign w = $bits(enum {A, B}), k = $bits(enum {G, H = 7});\n"
            "  int y = B;\n"
            "  initial v = $bits(enum {C, D = 5});\n"
            "  initial if (1) u = $bits(type(enum logic [1:0] {E = 2, F}));\n"
            "  initial #1 $display(\"%0d %0d %0d %0d %0d %0d %0d\",\n"
            "                      w, y, v, D, u, F, k + H);\n")
        .append(place.close);
    EXPECT_EQ(Printed(design), "32 1 32 5 2 3 39\n");
  }
}

TEST(StatementOperandEnumerationSim, AlwaysStatementDeclaresInItsScope) {
  for (const Place& place : kDeclarationPlaces) {
    if (place.open.starts_with("program")) continue;
    std::string design(place.open);
    design
        .append(
            "  int x;\n"
            "  always_comb x = $bits(enum logic [3:0] {I = 9, J});\n"
            "  initial #1 $display(\"%0d %0d\", x, J);\n")
        .append(place.close);
    EXPECT_EQ(Printed(design), "4 10\n");
  }
}

}  // namespace
