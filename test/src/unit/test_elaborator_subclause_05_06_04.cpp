#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveElaboration, DirectivePersistsAcrossModulesIntoElab) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define WIDTH 16\n"
      "module other; endmodule\n"
      "module t;\n"
      "  parameter W = `WIDTH;\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "W") {
      EXPECT_EQ(p.resolved_value, 16);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(CompilerDirectiveElaboration, MacroFromOneElabInvisibleInAnother) {
  {
    ElabFixture f1;
    auto* d1 = ElaborateWithPreprocessor(
        "`define ONLY_IN_FIRST 32\n"
        "module a;\n"
        "  parameter P = `ONLY_IN_FIRST;\n"
        "endmodule\n",
        f1);
    ASSERT_NE(d1, nullptr);
    EXPECT_FALSE(f1.has_errors);
  }

  ElabFixture f2;
  ElaborateWithPreprocessor(
      "module b;\n"
      "  parameter P = `ONLY_IN_FIRST;\n"
      "endmodule\n",
      f2);
  EXPECT_TRUE(f2.has_errors);
}

}  // namespace
