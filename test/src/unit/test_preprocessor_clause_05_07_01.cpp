#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(IntegerLiteralPreprocessor, MacroSubstitutionInLiteral) {
  auto r = ParseWithPreprocessor(
      "`define SIZE 8\n"
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = `SIZE'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(IntegerLiteralPreprocessor, MacroSubstitutionForValue) {
  auto r = ParseWithPreprocessor(
      "`define VAL 42\n"
      "module m;\n"
      "  int x;\n"
      "  initial x = `VAL;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(IntegerLiteralPreprocessor, MacroSubstitutionForBasedLiteral) {
  auto r = ParseWithPreprocessor(
      "`define LIT 8'hAB\n"
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = `LIT;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(IntegerLiteralPreprocessor, MacroSubstitutionForUnbasedUnsized) {
  auto r = ParseWithPreprocessor(
      "`define ALLONES '1\n"
      "module m;\n"
      "  logic [7:0] x;\n"
      "  assign x = `ALLONES;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(IntegerLiteralPreprocessor, MacroSubstitutionPreservesText) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define WIDTH 16\n"
      "`define BASE 'h\n"
      "int x = `WIDTH `BASE CAFE;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("16"), std::string::npos);
}

}  // namespace
