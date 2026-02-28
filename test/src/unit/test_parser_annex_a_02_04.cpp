// Annex A.2.4: Declaration assignments

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- net_decl_assignment ---
// net_identifier { unpacked_dimension } [ = expression ]
TEST(ParserA24, NetDeclAssignmentBasic) {
  auto r = Parse("module m; wire w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_EQ(item->init_expr, nullptr);  // No initializer
}

}  // namespace
