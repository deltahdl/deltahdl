// §23.3.2.1: Connecting module instance ports by ordered list

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.4 -- Instantiations
// =============================================================================
TEST(ParserAnnexA, A4ModuleInstPositional) {
  auto r = Parse("module m; sub u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
}

}  // namespace
