#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(InterfaceInstantiationGrammar, InterfaceInstArray) {
  auto r = Parse("module m; my_if u0 [3:0] (.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

}  // namespace
