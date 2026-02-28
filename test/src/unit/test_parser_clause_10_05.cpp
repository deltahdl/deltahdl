// §10.5: Variable declaration assignment (variable initialization)

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA24, VarDeclAssignmentWithInit) {
  auto r = Parse("module m; int x = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  EXPECT_NE(item->init_expr, nullptr);
}

}  // namespace
