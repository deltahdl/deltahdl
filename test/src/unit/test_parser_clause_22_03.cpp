#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, ResetallDirective) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`resetall\n"
                              "module t;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, ResetallBeforeMultipleModules) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`resetall\n"
                              "module m1;\n"
                              "endmodule\n"
                              "module m2;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, ResetallBetweenModulesResetsDefaultNettype) {
  auto r = ParseWithPreprocessor(
      "`default_nettype none\n"
      "module m1; endmodule\n"
      "`resetall\n"
      "module m2; endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->default_nettype, NetType::kWire);
}

TEST(CompilerDirectiveParsing, ResetallPreservesMacrosForParsing) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define WIDTH 8\n"
                              "`resetall\n"
                              "module t;\n"
                              "  logic [`WIDTH-1:0] data;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, ResetallInsideExcludedBranchProducesValidParse) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`ifdef UNDEF\n"
                              "`resetall\n"
                              "`endif\n"
                              "module t; endmodule\n"));
}

TEST(CompilerDirectiveParsing, ResetallResetsTimescaleForParsing) {
  auto r = ParseWithPreprocessor(
      "`timescale 1ns / 1ps\n"
      "`resetall\n"
      "module t; endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->default_decay_time_infinite);
}

TEST(CompilerDirectiveParsing, MultipleResetallBetweenModulesValid) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`resetall\n"
                              "module m1; endmodule\n"
                              "`resetall\n"
                              "module m2; endmodule\n"
                              "`resetall\n"));
}

}  // namespace
