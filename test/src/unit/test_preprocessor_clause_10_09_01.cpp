// §10.9.1: Array assignment patterns

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(Lexical, AssignmentPattern_Positional) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  logic [3:0] a;\n"
      "  initial a = '{1, 0, 1, 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, AssignmentPattern_Named) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  initial begin\n"
      "    logic [7:0] x;\n"
      "    x = '{default: 'x};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// ===========================================================================
// §10.9-10.10: Assignment pattern evaluation
// ===========================================================================
TEST(Lexical, AssignmentPattern_DefaultZero) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  initial a = '{default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // Should parse without error.
  ASSERT_EQ(r.cu->modules.size(), 1);
}

}  // namespace
