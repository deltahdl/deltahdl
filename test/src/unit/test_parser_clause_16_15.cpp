#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(SourceText, DefaultDisableIff) {
  auto r = Parse(
      "module m;\n"
      "  default disable iff rst;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind,
            ModuleItemKind::kDefaultDisableIff);
  EXPECT_NE(r.cu->modules[0]->items[0]->init_expr, nullptr);
}

}  // namespace
