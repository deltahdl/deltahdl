#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(OperatorElaboration, ModulePathOperatorsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a && b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A conditional expression mixing the allowed operand classes (input port,
// locally defined net, and specify parameter) must elaborate cleanly.
TEST(OperatorElaboration, ModulePathOperandClassesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  wire en;\n"
      "  specify\n"
      "    specparam SP = 1;\n"
      "    if (a && en && SP) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
