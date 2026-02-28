// §15.5.4: Event sequencing: wait_order()

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §15.5.4: action_block in wait_order statement
TEST(ParserA603, ActionBlockWaitOrder) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order (a, b, c) $display(\"ok\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
}

// §15.5.4: action_block in wait_order with else clause
TEST(ParserA603, ActionBlockWaitOrderElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order (a, b) else $display(\"out of order\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
}

}  // namespace
