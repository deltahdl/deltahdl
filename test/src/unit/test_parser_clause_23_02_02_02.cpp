

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ModuleDeclaration, EmptyPortListParens) {
  auto r = Parse("module m(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

}  // namespace
