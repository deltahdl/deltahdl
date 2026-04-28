#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §5.6.4: "The directive shall remain in effect for the rest of the
// compilation unit."  A `define declared before an unrelated module
// remains in effect when a later module is elaborated — its parameter
// resolves to the macro's value.
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

// §5.6.4: "A compiler directive shall not affect other compilation units."
// Two independent elaboration calls each construct their own preprocessor;
// macros defined in the first are invisible in the second.
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
  // A second elaboration with no `define for ONLY_IN_FIRST must fail to
  // elaborate the parameter (the macro never existed in this CU).
  ElabFixture f2;
  ElaborateWithPreprocessor(
      "module b;\n"
      "  parameter P = `ONLY_IN_FIRST;\n"
      "endmodule\n",
      f2);
  EXPECT_TRUE(f2.has_errors);
}

// §5.6.4: "The compiler behavior dictated by a compiler directive shall
// take effect as soon as the compiler reads the directive."  A `define
// read before a module's parameter reaches elaboration with the macro
// value resolved.
TEST(CompilerDirectiveElaboration, DirectiveTakesEffectBeforeParamResolve) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define VAL 7\n"
      "module m;\n"
      "  parameter P = `VAL;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 7);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
