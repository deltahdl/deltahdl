// §9.4.4: Level-sensitive sequence controls

#include "fixture_parser.h"

using namespace delta;

struct ParseResult9c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9c Parse(const std::string& src) {
  ParseResult9c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// =============================================================================
// §9.4.4 -- Level-sensitive sequence controls
// =============================================================================
TEST(ParserSection9, WaitSequenceTriggered) {
  auto r = Parse(
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait(abc.triggered);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection9, WaitSequenceTriggeredOr) {
  auto r = Parse(
      "module m;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(negedge clk) c ##1 d;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait(s1.triggered || s2.triggered);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// =============================================================================
// LRM section 9.4.4 -- Level-sensitive sequence controls
// Wait on sequence.triggered to synchronize with sequence end point.
// =============================================================================
TEST(ParserSection9c, WaitSequenceTriggeredWithAction) {
  // After wait(seq.triggered), execute a procedural statement.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence req_ack;\n"
              "    @(posedge clk) req ##[1:5] ack;\n"
              "  endsequence\n"
              "  initial begin\n"
              "    wait(req_ack.triggered);\n"
              "    $display(\"handshake complete\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection9c, WaitTriggeredInLoop) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s;\n"
              "    @(posedge clk) a ##1 b;\n"
              "  endsequence\n"
              "  initial begin\n"
              "    forever begin\n"
              "      wait(s.triggered);\n"
              "      count = count + 1;\n"
              "      @(posedge clk);\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
