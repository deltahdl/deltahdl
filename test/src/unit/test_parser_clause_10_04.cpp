#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

static ModuleItem* FindInitialBlock(ParseResult& r) {
  return FindItemByKind(r, ModuleItemKind::kInitialBlock);
}

TEST(SchedulingSemanticsParsing, MixBlockingNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, d;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    c <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* init_item = FindInitialBlock(r);
  ASSERT_NE(init_item, nullptr);
  auto* body = init_item->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

}  // namespace
