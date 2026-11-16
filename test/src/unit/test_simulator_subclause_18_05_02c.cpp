#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunSrc(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

TEST(PureConstraintCases, APrototypeAndExternalBlockImplementationHolds) {
  EXPECT_EQ(RunSrc("virtual class B;\n"
                   "  rand bit [7:0] x;\n"
                   "  pure constraint c;\n"
                   "endclass\n"
                   "class D extends B;\n"
                   "  constraint c;\n"
                   "endclass\n"
                   "constraint D::c { x == 77; }\n"
                   "module t;\n"
                   "  int i, held = 0;\n"
                   "  initial begin\n"
                   "    static D d = new;\n"
                   "    for (i = 0; i < 16; i++)\n"
                   "      if (d.randomize() && d.x == 77) held++;\n"
                   "    $display(\"%0d\", held);\n"
                   "  end\n"
                   "endmodule\n"),
            "16\n");
}

TEST(PureConstraintCases, AConstraintRedeclaredPureNoLongerBinds) {
  EXPECT_EQ(RunSrc("class B;\n"
                   "  rand bit [7:0] x;\n"
                   "  constraint c { x == 5; }\n"
                   "endclass\n"
                   "virtual class M extends B;\n"
                   "  pure constraint c;\n"
                   "endclass\n"
                   "class D extends M;\n"
                   "  constraint c { x == 9; }\n"
                   "endclass\n"
                   "module t;\n"
                   "  int i, held = 0;\n"
                   "  initial begin\n"
                   "    static D d = new;\n"
                   "    for (i = 0; i < 16; i++)\n"
                   "      if (d.randomize() && d.x == 9) held++;\n"
                   "    $display(\"%0d\", held);\n"
                   "  end\n"
                   "endmodule\n"),
            "16\n");
}

}  // namespace
