#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaboration, AssocArrayRealIndex_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[real];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, AssocArrayShortrealIndex_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[shortreal];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, AssocArrayTypedefIndex_Allowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef bit [3:0] nibble_t;\n"
      "  int aa[nibble_t];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_TRUE(v.is_assoc);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(Elaboration, AssocArrayIntIndex_Allowed) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  int aa[int];\n"
             "endmodule\n"));
}

}  // namespace
