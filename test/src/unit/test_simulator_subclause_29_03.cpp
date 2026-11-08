#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kAnd2Definition =
    "primitive and2 (y, a, b);\n"
    "  output y;\n"
    "  input a, b;\n"
    "  table\n"
    "    1 1 : 1 ;\n"
    "    0 ? : 0 ;\n"
    "    ? 0 : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

constexpr const char* kAnd2User =
    "module top;\n"
    "  reg a, b;\n"
    "  wire y;\n"
    "  and2 u(y, a, b);\n"
    "  initial begin\n"
    "    a = 1; b = 1; #1 $display(\"%b\", y);\n"
    "    b = 0; #1 $display(\"%b\", y);\n"
    "  end\n"
    "endmodule\n";

TEST(ExternUdpDeclarationRun,
     ExternPrototypeBeforeTheDefinitionIsOnePrimitive) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string("extern primitive and2 (y, a, b);\n") +
                           kAnd2User + kAnd2Definition,
                       f),
            "1\n0\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ExternUdpDeclarationRun, ExternPrototypeAfterTheDefinitionIsOnePrimitive) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kAnd2Definition) + kAnd2User +
                           "extern primitive and2 (y, a, b);\n",
                       f),
            "1\n0\n");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
