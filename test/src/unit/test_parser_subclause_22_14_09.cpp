#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing,
     BeginKeywords1800_2017_InheritedKeywordStaysReserved) {
  auto r = ParseWithPreprocessor(
      "`begin_keywords \"1800-2017\"\n"
      "module t;\n"
      "  logic soft;\n"
      "endmodule\n"
      "`end_keywords\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got 'soft'", 3, "6.8"));
}

TEST(CompilerDirectiveParsing,
     BeginKeywords1800_2023_InheritedKeywordStaysReserved) {
  auto r = ParseWithPreprocessor(
      "`begin_keywords \"1800-2023\"\n"
      "module t;\n"
      "  logic soft;\n"
      "endmodule\n"
      "`end_keywords\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got 'soft'", 3, "6.8"));
}

TEST(CompilerDirectiveParsing, BeginKeywords1800_2009_SoftIsFreeIdentifier) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2009\"\n"
                              "module t;\n"
                              "  logic soft;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(CompilerDirectiveParsing, BeginKeywords1800_2017_AddsNoNewKeyword) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2017\"\n"
                              "module t;\n"
                              "  logic user_signal;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(CompilerDirectiveParsing, BeginKeywords1800_2023_AddsNoNewKeyword) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2023\"\n"
                              "module t;\n"
                              "  logic user_signal;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

}  // namespace
