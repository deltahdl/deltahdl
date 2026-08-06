#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(AssignmentPatternPreprocessing, PositionalAssignmentPattern) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  logic [3:0] a;\n"
      "  initial a = '{1, 0, 1, 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(AssignmentPatternPreprocessing, NamedAssignmentPattern) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  initial begin\n"
      "    logic [7:0] x;\n"
      "    x = '{default: 'x};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssignmentPatternPreprocessing, MacroExpansionPreservesPattern) {
  auto r = ParseWithPreprocessor(
      "`define ZEROS '{default: 0}\n"
      "module top;\n"
      "  logic [7:0] a;\n"
      "  initial a = `ZEROS;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
