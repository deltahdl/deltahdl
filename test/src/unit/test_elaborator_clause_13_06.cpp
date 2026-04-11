#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ImportExportElaboration, DpiImportFunctionElaborates) {
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

TEST(ImportExportElaboration, DpiImportTaskElaborates) {
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

TEST(ImportExportElaboration, DpiExportFunctionElaborates) {
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

TEST(ImportExportElaboration, DpiImportContextElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" context function void c_callback();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ImportExportElaboration, DpiImportPureElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" pure function int c_abs(int x);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ImportExportElaboration, DpiImportWithCNameElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" my_c_func = function int sv_wrapper(int x);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ImportExportElaboration, DpiExportTaskElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  task my_task(); endtask\n"
      "  export \"DPI-C\" task my_task;\n"
      "endmodule\n"));
}

TEST(ImportExportElaboration, MultipleImportsElaborate) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(int a, int b);\n"
      "  import \"DPI-C\" function int c_sub(int a, int b);\n"
      "endmodule\n"));
}

TEST(ImportExportElaboration, ImportAndExportCoexistElaborate) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  import \"DPI-C\" function int c_func(int x);\n"
      "  function void sv_func(); endfunction\n"
      "  export \"DPI-C\" function sv_func;\n"
      "endmodule\n"));
}

TEST(ImportExportElaboration, ImportedFunctionInExpressionElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  import \"DPI-C\" function int c_mul(int a, int b);\n"
      "  int y;\n"
      "  initial y = c_mul(3, 4) + 1;\n"
      "endmodule\n"));
}

}  // namespace
