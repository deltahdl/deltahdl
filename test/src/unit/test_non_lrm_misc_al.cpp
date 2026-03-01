// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// statement ::= [ block_identifier : ] { attribute_instance } statement_item
// ---------------------------------------------------------------------------
// §9.3.5: statement with block_identifier label
TEST(ParserA604, StatementWithLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    my_label: a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->label, "my_label");
}

}  // namespace
