#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA26, ElabFunctionAutomaticLifetime) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function automatic int fact(input int n);\n"
      "    if (n <= 1) return 1;\n"
      "    return n;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §13.4.2: Static function elaborates without error.
TEST(Elab1342, StaticFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function static int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.2: Static var in automatic function elaborates.
TEST(Elab1342, StaticVarInAutoFuncElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int get_id();\n"
      "    static int next_id = 0;\n"
      "    next_id = next_id + 1;\n"
      "    return next_id;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.2: Automatic var in static function elaborates.
TEST(Elab1342, AutoVarInStaticFuncElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function static int compute(int x);\n"
      "    automatic int tmp = x * 2;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.2: Default lifetime function (no qualifier) elaborates.
TEST(Elab1342, DefaultLifetimeFuncElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int adder(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
