// §11.4.14: Streaming operators (pack/unpack)

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § primary — streaming_concatenation
TEST(ParserA84, PrimaryStreamingConcat) {
  auto r = Parse("module m;\n"
                 "  logic [31:0] a;\n"
                 "  logic [31:0] b;\n"
                 "  initial b = {<< 8 {a}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
}
// =========================================================================
// Section 11.4.14 -- Streaming operators
// =========================================================================
TEST(ParserSection11, StreamingRight) {
  auto r = Parse("module t;\n"
                 "  initial x = {>> {a, b, c}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
}

TEST(ParserSection11, StreamingWithSliceSize) {
  auto r = Parse("module t;\n"
                 "  initial x = {<< 8 {a, b}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_NE(rhs->lhs, nullptr); // slice_size
}

// § streaming_concatenation ::=
//     { stream_operator [ slice_size ] stream_concatenation }
TEST(ParserA81, StreamingConcatLeftShift) {
  auto r = Parse("module m; initial x = {<< {a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kLtLt);
}

TEST(ParserA81, StreamingConcatRightShift) {
  auto r = Parse("module m; initial x = {>> {a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kGtGt);
}
// --- Streaming concatenation ---
TEST(ParserSection11, Sec11_1_StreamingConcatLeftShift) {
  auto r = Parse("module t;\n"
                 "  initial x = {<< {a, b}};\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
  EXPECT_EQ(rhs->elements.size(), 2u);
}
TEST(ParserSection6, BitStreamCastStreaming) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    byte a;\n"
                 "    int b;\n"
                 "    b = int'({<< byte {a}});\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

} // namespace
