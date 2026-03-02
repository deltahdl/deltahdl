// §11.4.14.4: Streaming dynamically sized data

#include "fixture_parser.h"

using namespace delta;

struct ParseResult11d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11d Parse(const std::string& src) {
  ParseResult11d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// --- Streaming concatenation with clause (§11.4.14.4) ---
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

// § stream_expression ::= expression [ with [ array_range_expression ] ]
TEST(ParserA81, StreamExpressionWithArrayRange) {
  auto r = Parse("module m; initial x = {<< {a with [3]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
}

// § array_range_expression ::= expression : expression
TEST(ParserA81, StreamExprWithFixedRange) {
  auto r = Parse("module m; initial x = {<< {a with [3:0]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § array_range_expression ::= expression +: expression
TEST(ParserA81, StreamExprWithPlusRange) {
  auto r = Parse("module m; initial x = {<< {a with [0+:4]}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
