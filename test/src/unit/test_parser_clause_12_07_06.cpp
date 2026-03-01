// §12.7.6: The forever-loop

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Forever loop wrapping a timing control.
TEST(ParserSection12, ForeverWithTimingControl) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    forever begin\n"
              "      @(posedge clk);\n"
              "      x = ~x;\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// A.6.8 Looping statements — loop_statement
// =============================================================================
// --- forever statement_or_null ---
TEST(ParserA608, ForeverLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin forever #5 clk = ~clk; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
  EXPECT_NE(stmt->body, nullptr);
}

}  // namespace
