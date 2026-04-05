#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(StreamingDynamicDataParsing, StreamingWithPartSelect) {
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

TEST(StreamingDynamicDataParsing, StreamingWithSimpleIndex) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4], out[4];\n"
      "  initial {<< int {out with [3]}} = arr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StreamingDynamicDataParsing, StreamExpressionWithArrayRange) {
  auto r = Parse("module m; initial x = {<< {a with [3]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
}

TEST(StreamingDynamicDataParsing, StreamExprWithFixedRange) {
  auto r = Parse("module m; initial x = {<< {a with [3:0]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StreamingDynamicDataParsing, StreamExprWithPlusRange) {
  auto r = Parse("module m; initial x = {<< {a with [0+:4]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StreamingDynamicDataParsing, StreamExprWithMinusRange) {
  auto r = Parse("module m; initial x = {<< {a with [7-:4]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StreamingDynamicDataParsing, WithClauseInRightShiftStreaming) {
  auto r = Parse("module m; initial x = {>> {a with [3]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kGtGt);
}

TEST(StreamingDynamicDataParsing, WithClauseAmongMultipleElements) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] hdr, crc;\n"
      "  logic [7:0] payload[8];\n"
      "  int len;\n"
      "  initial x = {<< byte {hdr, payload with [0 +: len], crc}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StreamingDynamicDataParsing, WithClauseProducesStreamingConcatNode) {
  auto r = Parse(
      "module m;\n"
      "  int arr[4];\n"
      "  initial x = {>> int {arr with [1:2]}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
}

TEST(StreamingDynamicDataParsing, WithClauseAsUnpackTarget) {
  auto r = Parse(
      "module m;\n"
      "  byte q[$];\n"
      "  initial {<< byte {q with [0 +: 4]}} = src;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
