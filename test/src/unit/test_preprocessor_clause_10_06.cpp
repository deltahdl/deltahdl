#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ProceduralContinuousAssignmentPreprocessing, ForceAndRelease) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module m;\n"
      "  initial begin\n"
      "    force q = 1;\n"
      "    release q;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ProceduralContinuousAssignmentPreprocessing, AssignAndDeassign) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module m;\n"
      "  initial begin\n"
      "    assign q = d;\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n"));
}

}  // namespace
