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

}  // namespace
