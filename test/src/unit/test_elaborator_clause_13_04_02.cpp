#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(FunctionLifetimeElaboration, DefaultLifetimeFunctionElaborates) {
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

TEST(FunctionLifetimeElaboration, RecursiveAutomaticFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int factorial(int n);\n"
      "    if (n <= 1) return 1;\n"
      "    return n * factorial(n - 1);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionLifetimeElaboration, StaticVarNonConstantInitializerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function automatic int bad_init(int x);\n"
      "    static int s = x;\n"
      "    return s;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}
