#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(AssocArrayElaboration, MarkedAssociative) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa[int]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_assoc);
}

TEST(AssocArrayElaboration, ElementWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [7:0] aa[int]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_EQ(v.width, 8u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(AssocArrayElaboration, MultipleArrays) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a[int];\n"
             "  string b[string];\n"
             "endmodule\n"));
}

}
