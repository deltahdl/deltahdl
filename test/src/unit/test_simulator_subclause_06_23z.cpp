#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr std::string_view kWidthClass =
    "class X #(type T = int);\n"
    "  static function int w(); T v; return $bits(v); endfunction\n"
    "endclass\n"
    "module top;\n"
    "logic c = 0;\n"
    "logic [4:0] m;\n"
    "logic [1:0] k2;\n"
    "real r;\n"
    "int held = 0;\n"
    "initial begin\n"
    "  #1 c = 1;\n"
    "  #1 $display(\"%b\", held);\n"
    "end\n";

std::string Printed(std::string_view items) {
  SimFixture f;
  return RunCapture(
      std::string(kWidthClass).append(items).append("endmodule\n"), f);
}

std::string Held(std::string_view bits) {
  return std::string(32 - bits.size(), '0').append(bits).append("\n");
}

TEST(ScopePrefixUntypedFormalTypeRefSim, TakesEachInstancesActualType) {
  EXPECT_EQ(
      Printed("property p(x); @(posedge c) X#(type(x))::w() == 5; endproperty\n"
              "property t(x); @(posedge c) 1 ##0 X#(type(x))::w() == 5;\n"
              "endproperty\n"
              "sequence q(x); X#(type(x))::w() == 5; endsequence\n"
              "property e(x); @(posedge c) X#(type(x + 9'd0))::w() == 9;\n"
              "endproperty\n"
              "property two(x, int b); @(posedge c) X#(type(x))::w() == b;\n"
              "endproperty\n"
              "property d(int b, x = m); X#(type(x))::w() == b; endproperty\n"
              "assert property (p(m)) held[0] = 1;\n"
              "assert property (t(m)) held[1] = 1;\n"
              "assert property (@(posedge c) q(m)) held[2] = 1;\n"
              "assert property (e(m)) held[3] = 1;\n"
              "assert property (two(m, 5)) held[4] = 1;\n"
              "assert property (two(k2, 2)) held[5] = 1;\n"
              "assert property (@(posedge c) d(5)) held[6] = 1;\n"
              "assert property (two(r, 64)) held[7] = 1;\n"),
      Held("11111111"));
}

TEST(ScopePrefixUntypedFormalTypeRefSim, TakesALetsActualType) {
  EXPECT_EQ(Printed("let l(x) = X#(type(x))::w();\n"
                    "initial begin\n"
                    "  let b(x) = X#(type(x))::w();\n"
                    "  $display(\"%0d %0d %0d\", l(m), l(k2), b(m));\n"
                    "end\n"),
            "5 2 5\n" + Held(""));
}

TEST(ScopePrefixUntypedFormalTypeRefSim, FormalHidesTheScopesName) {
  EXPECT_EQ(
      Printed("logic [8:0] x;\n"
              "property h(x); @(posedge c) X#(type(x))::w() == 5; endproperty\n"
              "let l(x) = X#(type(x))::w();\n"
              "assert property (h(m)) held[0] = 1;\n"
              "initial $display(\"%0d\", l(m));\n"),
      "5\n" + Held("1"));
}

}  // namespace
