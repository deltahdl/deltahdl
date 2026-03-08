#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection11, StreamingWithPartSelect) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] pkt[10];\n"
      "  logic [7:0] o_header, o_crc;\n"
      "  int o_len;\n"
      "  logic [7:0] o_data[8];\n"
      "  initial begin\n"
      "    {<< 8 {o_header, o_len, o_data with [0 +: o_len], o_crc}} = pkt;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, StreamingWithSimpleIndex) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4], out[4];\n"
      "  initial {<< int {out with [3]}} = arr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA81, StreamExpressionWithArrayRange) {
  auto r = Parse("module m; initial x = {<< {a with [3]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
}

TEST(ParserA81, StreamExprWithFixedRange) {
  auto r = Parse("module m; initial x = {<< {a with [3:0]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA81, StreamExprWithPlusRange) {
  auto r = Parse("module m; initial x = {<< {a with [0+:4]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA81, StreamExprWithMinusRange) {
  auto r = Parse("module m; initial x = {<< {a with [7-:4]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
