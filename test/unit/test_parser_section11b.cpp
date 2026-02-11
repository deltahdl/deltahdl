#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult11b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11b Parse(const std::string& src) {
  ParseResult11b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// --- Empty args in system calls (§20.2/§21.2) ---

TEST(ParserSection11, SystemCallEmptyArgs) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(5,,2,,3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, SystemCallLeadingEmptyArg) {
  auto r = Parse(
      "module t;\n"
      "  initial $display(,\"hello\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- Bit-select on concatenation (§11.4.12) ---

TEST(ParserSection11, BitSelectOnConcat) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] a, b, c;\n"
      "  initial a = {b, c}[5:2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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
