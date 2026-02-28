// §9.2.2.2.2: always_comb compared to always @*

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult9i {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9i Parse(const std::string& src) {
  ParseResult9i result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// ---------------------------------------------------------------------------
// 29. Both always_comb and always @(*) in the same module with blocks.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_BothFormsWithBlocksInModule) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a, b, c, x, y;\n"
      "  always_comb begin\n"
      "    x = a + b;\n"
      "  end\n"
      "  always @(*) begin\n"
      "    y = b + c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* comb = NthAlwaysItem(r, 0);
  auto* star = NthAlwaysItem(r, 1);
  ASSERT_NE(comb, nullptr);
  ASSERT_NE(star, nullptr);
  EXPECT_EQ(comb->always_kind, AlwaysKind::kAlwaysComb);
  EXPECT_EQ(star->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(comb->body, nullptr);
  ASSERT_NE(star->body, nullptr);
  EXPECT_EQ(comb->body->kind, StmtKind::kBlock);
  EXPECT_EQ(star->body->kind, StmtKind::kBlock);
}

// ---------------------------------------------------------------------------
// 30. Full combo module: always_comb, always @*, always @(*), with
//     case, if-else, and variable declarations, verifying all parse OK.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_FullComboModuleParseOk) {
  EXPECT_TRUE(
      ParseOk("module combo_module;\n"
              "  logic [3:0] sel, a, b, c, d;\n"
              "  logic [3:0] out1, out2, out3;\n"
              "  always_comb begin\n"
              "    int tmp;\n"
              "    tmp = a + b;\n"
              "    case (sel)\n"
              "      4'b0001: out1 = a;\n"
              "      4'b0010: out1 = b;\n"
              "      default: out1 = 0;\n"
              "    endcase\n"
              "  end\n"
              "  always @* begin\n"
              "    int tmp2;\n"
              "    tmp2 = c - d;\n"
              "    if (sel[0])\n"
              "      out2 = c;\n"
              "    else\n"
              "      out2 = d;\n"
              "  end\n"
              "  always @(*) begin\n"
              "    out3 = a ^ b ^ c ^ d;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
