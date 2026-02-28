// §10.4: Procedural assignments

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// Return all statements from the first initial block's begin/end.
static std::vector<Stmt*> AllInitialStmts(ParseResult& r) {
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  if (!item || !item->body) return {};
  if (item->body->kind == StmtKind::kBlock) return item->body->stmts;
  return {item->body};
}

namespace {

// =============================================================================
// Integration: Mixing blocking and nonblocking in the same block
// =============================================================================
TEST(ParserA602, MixedAssignments_BlockingAndNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b <= 2;\n"
      "    c += 3;\n"
      "    d <= #10 4;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_EQ(stmts.size(), 4u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kBlockingAssign);  // compound
  EXPECT_EQ(stmts[3]->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmts[3]->delay, nullptr);
}

}  // namespace
