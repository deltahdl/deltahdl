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

}  // namespace
