// §29.3's UDP declarations, as a running simulation instantiates them.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The definition of `and2`, a two-input AND.
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

// A module instantiating `and2` and printing y for 1 & 1 and then 1 & 0.
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

// Syntax 29-1 (printed page 861): a udp_declaration may be `extern
// udp_nonansi_declaration`, the primitive's ports without its body, so an
// extern declaration of `and2` ahead of the module and the full definition
// after it are one primitive, which the module instantiates. The definition
// was reported as a second one, "duplicate definition of 'and2' (§3.13)".
TEST(ExternUdpDeclarationRun,
     ExternPrototypeBeforeTheDefinitionIsOnePrimitive) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string("extern primitive and2 (y, a, b);\n") +
                           kAnd2User + kAnd2Definition,
                       f),
            "1\n0\n");
  EXPECT_FALSE(f.has_errors);
}

// The same with the prototype after the definition: the instance still
// takes the definition's table.
TEST(ExternUdpDeclarationRun, ExternPrototypeAfterTheDefinitionIsOnePrimitive) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kAnd2Definition) + kAnd2User +
                           "extern primitive and2 (y, a, b);\n",
                       f),
            "1\n0\n");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
