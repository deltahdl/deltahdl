// §23.2

#include "fixture_parser.h"

using namespace delta;

namespace {

// §3.1 — End labels on design elements parse correctly.
TEST(ModuleEndLabel, EndLabelMatchesModuleName) {
  auto r = Parse("module foo; endmodule : foo\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "foo");
}

}  // namespace
