#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ContinuousAssignPreprocessor, BasicContinuousAssign) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n"));
}

TEST(ContinuousAssignPreprocessor, ContinuousAssignWithStrengthAndDelay) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module m;\n"
      "  wire a, b;\n"
      "  assign (strong0, weak1) #10 a = b;\n"
      "endmodule\n"));
}

TEST(ContinuousAssignPreprocessor, ListOfNetAssignments) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign a = b, c = d;\n"
      "endmodule\n"));
}

TEST(ContinuousAssignPreprocessor, MacroExpandedRhs) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define VAL 1'b1\n"
      "module m;\n"
      "  wire y;\n"
      "  assign y = `VAL;\n"
      "endmodule\n"));
}

TEST(ContinuousAssignPreprocessor, ConditionalCompilationAroundAssign) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define USE_ASSIGN\n"
      "module m;\n"
      "  wire a, b;\n"
      "`ifdef USE_ASSIGN\n"
      "  assign a = b;\n"
      "`endif\n"
      "endmodule\n"));
}

}  // namespace
