#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DefaultArgumentElaboration, MissingArgNoDefaultError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = add(1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(DefaultArgumentElaboration, MissingArgWithDefaultOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int inc(int a, int step = 1);\n"
      "    return a + step;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = inc(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultArgumentElaboration, AllDefaultsNoArgsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute(int a = 1, int b = 2);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = compute();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
