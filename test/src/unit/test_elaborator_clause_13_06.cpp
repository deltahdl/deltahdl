#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elab1360, DpiImportFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(int a, int b);\n"
      "  int x;\n"
      "  initial x = c_add(1, 2);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab1360, DpiImportTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" task c_print(int val);\n"
      "  initial c_print(42);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab1360, DpiExportFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int sv_func(int x); return x + 1; endfunction\n"
      "  export \"DPI-C\" function sv_func;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab1360, DpiImportContextElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" context function void c_callback();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab1360, DpiImportPureElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" pure function int c_abs(int x);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab1360, DpiImportWithCNameElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" my_c_func = function int sv_wrapper(int x);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}
