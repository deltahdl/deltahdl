#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  // The macro being invisible here shows up as the preprocessor's own
  // undefined-macro report, at src/preprocessor/preprocessor_inline.cpp:261,
  // so this case reaches its subject through a source that does not get
  // through the preprocessor.
  ElaborateWithPreprocessorAllowingParseErrors(
      "module b;\n"
      "  parameter P = `ONLY_IN_FIRST;\n"
      "endmodule\n",
      f2);
  EXPECT_TRUE(ReportedError(f2.diag.Diagnostics(),
                            "undefined macro 'ONLY_IN_FIRST'", 2, "22.5.1"));
}

}  // namespace
