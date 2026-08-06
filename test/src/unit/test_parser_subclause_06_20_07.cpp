#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DollarConstantParsing, DollarInQueueDimension) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DollarConstantParsing, DollarAssignedToParameter) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  parameter p = $;\n"
               "endmodule\n"));
}

TEST(DollarConstantParsing, DollarParameterInPortList) {
  auto r = Parse("module m #(parameter int P = $); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "P");
}

}  // namespace
