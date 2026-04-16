#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ExternModulePreprocessing, ExternModule) {
  auto r = ParseWithPreprocessor("extern module m(input logic a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
}

TEST(ExternModulePreprocessing, ExternNonAnsiPorts) {
  auto r = ParseWithPreprocessor("extern module m (a, b, c);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
}

TEST(ExternModulePreprocessing, ExternWithParameters) {
  auto r = ParseWithPreprocessor(
      "extern module a #(parameter size = 8)\n"
      "  (input [size:0] x, output logic y);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
}

TEST(ExternModulePreprocessing, ExternFollowedByDefinition) {
  auto r = ParseWithPreprocessor(
      "extern module m(input logic a, output logic b);\n"
      "module m(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_FALSE(r.cu->modules[1]->is_extern);
}

}  // namespace
