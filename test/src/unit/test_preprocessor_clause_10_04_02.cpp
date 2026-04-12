#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(NonblockingAssignPreprocessing, MacroExpandedRhs) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define DATA_VAL 8'hFF\n"
      "module m;\n"
      "  logic [7:0] q;\n"
      "  initial q <= `DATA_VAL;\n"
      "endmodule\n"));
}

TEST(NonblockingAssignPreprocessing, MacroExpandedLhs) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define REG_Q q\n"
      "module m;\n"
      "  logic [7:0] q, d;\n"
      "  initial `REG_Q <= d;\n"
      "endmodule\n"));
}

TEST(NonblockingAssignPreprocessing, ConditionalCompilationAroundNba) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define USE_NBA\n"
      "module m;\n"
      "  logic [7:0] q, d;\n"
      "  initial begin\n"
      "`ifdef USE_NBA\n"
      "    q <= d;\n"
      "`endif\n"
      "  end\n"
      "endmodule\n"));
}

TEST(NonblockingAssignPreprocessing, MacroExpandedFullStatement) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "`define NBA_STMT q <= d\n"
      "module m;\n"
      "  logic [7:0] q, d;\n"
      "  initial `NBA_STMT;\n"
      "endmodule\n"));
}

}  // namespace
