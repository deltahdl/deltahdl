#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;
namespace {

// 12.7.6: a forever loop should be used in conjunction with a timing control,
// so the repeated statement here is delay-controlled. The A.6.8 file carries
// the plain assignment body.
TEST(LoopSyntaxParsing, ForeverLoopWithTimingControlledBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    forever #5 clk = ~clk;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(LoopSyntaxParsing, ForeverNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin forever ; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
}

TEST(LoopSyntaxParsing, ForeverLoopWithBlock) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    forever begin\n"
      "      @(posedge clk);\n"
      "      x = x + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

TEST(LoopSyntaxParsing, ErrorForeverMissingBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    forever\n"
      "  end\n"
      "endmodule\n");
  // §12.7.6 gives forever no report of its own for a missing body: the parser
  // asks for the statement and the `end` on line 4 is read as an expression,
  // so the report is the §11.2 one.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 4, "11.2"));
}

}  // namespace
