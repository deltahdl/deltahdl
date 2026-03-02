// Annex A.8.5: Expression left-side values

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

static ModuleItem* FirstContAssign(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// A.8.5 Expression left-side values — net_lvalue
// =============================================================================
// § net_lvalue — ps_or_hierarchical_net_identifier constant_select (simple net)
TEST(ParserA85, NetLvalueSimpleIdent) {
  auto r = Parse("module m; wire a, b; assign a = b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ca->assign_lhs->text, "a");
}

}  // namespace
