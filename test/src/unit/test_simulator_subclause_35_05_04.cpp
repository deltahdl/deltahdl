#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiRuntime, RegisterImportAndCall) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_add";
  func.sv_name = "sv_add";
  func.return_type = DataTypeKind::kInt;
  func.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() + args[1].AsInt());
  };
  rt.RegisterImport(func);

  EXPECT_EQ(rt.ImportCount(), 1u);
  EXPECT_TRUE(rt.HasImport("sv_add"));
  EXPECT_FALSE(rt.HasImport("missing"));

  auto result = rt.CallImport(
      "sv_add", {DpiArgValue::FromInt(10), DpiArgValue::FromInt(20)});
  EXPECT_EQ(result.AsInt(), 30);
}

TEST(DpiImportLowering, AnImportedFunctionOfTheDesignIsRegistered) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  import \"DPI-C\" function int add_one(input int a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dpi = f.ctx.GetDpiRuntime();
  ASSERT_NE(dpi, nullptr);
  EXPECT_TRUE(dpi->HasImport("add_one"));
}

TEST(DpiImportLowering, AnImportedFunctionCarriesItsFormalsDirections) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  import \"DPI-C\" function void swap(input int a, output int b,\n"
      "                                     inout int c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dpi = f.ctx.GetDpiRuntime();
  ASSERT_NE(dpi, nullptr);
  const DpiRtFunction* import = dpi->FindImport("swap");
  ASSERT_NE(import, nullptr);
  ASSERT_EQ(import->args.size(), 3u);
  EXPECT_EQ(import->args[0].direction, Direction::kInput);
  EXPECT_EQ(import->args[1].direction, Direction::kOutput);
  EXPECT_EQ(import->args[2].direction, Direction::kInout);
  EXPECT_EQ(import->args[1].type, DataTypeKind::kInt);
}

TEST(DpiImportLowering, AnImportedFunctionCarriesItsPackedFormalsWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  import \"DPI-C\" function void take_key(input bit [127:0] key,\n"
      "                                         input int n);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dpi = f.ctx.GetDpiRuntime();
  ASSERT_NE(dpi, nullptr);
  const DpiRtFunction* import = dpi->FindImport("take_key");
  ASSERT_NE(import, nullptr);
  ASSERT_EQ(import->args.size(), 2u);
  EXPECT_EQ(import->args[0].width, 128U);
  EXPECT_EQ(import->args[1].width, 0U);
}

TEST(DpiImportLowering, AFormalWithUnpackedDimensionsIsRecordedAsSuch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  import \"DPI-C\" function void take_arrays(input int open [],\n"
      "                                            input bit [7:0] b [0:3],\n"
      "                                            input bit [7:0] c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dpi = f.ctx.GetDpiRuntime();
  ASSERT_NE(dpi, nullptr);
  const DpiRtFunction* import = dpi->FindImport("take_arrays");
  ASSERT_NE(import, nullptr);
  ASSERT_EQ(import->args.size(), 3u);
  EXPECT_TRUE(import->args[0].has_unpacked_dimensions);
  EXPECT_TRUE(import->args[1].has_unpacked_dimensions);
  EXPECT_FALSE(import->args[2].has_unpacked_dimensions);
}

TEST(DpiImportLowering, ACallToAnUnresolvedImportIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  import \"DPI-C\" function int add_one(input int a);\n"
      "  int r;\n"
      "  initial r = add_one(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "imported subroutine 'add_one' is bound to no foreign implementation", 4,
      "35.5.4"));
}

TEST(DpiImportLowering, AnImportDeclaredInAPackageIsRegistered) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  import \"DPI-C\" function int p_add(input int a, input int b);\n"
      "endpackage\n"
      "module t;\n"
      "  import p::*;\n"
      "  int r;\n"
      "  initial r = p_add(50, 8);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dpi = f.ctx.GetDpiRuntime();
  ASSERT_NE(dpi, nullptr);
  EXPECT_TRUE(dpi->HasImport("p_add"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "imported subroutine 'p_add' is bound to no foreign implementation", 7,
      "35.5.4"));
}

TEST(DpiImportLowering, AnImportDeclaredInAPackageIsReachedThroughItsScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  import \"DPI-C\" function int p_mul(input int a, input int b);\n"
      "endpackage\n"
      "module t;\n"
      "  int r;\n"
      "  initial r = p::p_mul(7, 8);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "imported subroutine 'p_mul' is bound to no foreign implementation", 6,
      "35.5.4"));
}

TEST(DpiImportLowering, AnImportDeclaredInAChildModuleIsRegistered) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" function int m_get(input int a);\n"
      "  int r;\n"
      "  initial r = m_get(3);\n"
      "endmodule\n"
      "module t;\n"
      "  m u1();\n"
      "  m u2();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dpi = f.ctx.GetDpiRuntime();
  ASSERT_NE(dpi, nullptr);
  EXPECT_TRUE(dpi->HasImport("m_get"));
  EXPECT_EQ(dpi->ImportCount(), 1u);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "imported subroutine 'm_get' is bound to no foreign implementation", 4,
      "35.5.4"));
}

TEST(DpiImportLowering, AnImportDeclaredInAnInterfaceIsRegistered) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  import \"DPI-C\" function int i_sub(input int a);\n"
      "  int r;\n"
      "  initial r = i_sub(42);\n"
      "endinterface\n"
      "module t;\n"
      "  ifc i();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dpi = f.ctx.GetDpiRuntime();
  ASSERT_NE(dpi, nullptr);
  EXPECT_TRUE(dpi->HasImport("i_sub"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "imported subroutine 'i_sub' is bound to no foreign implementation", 4,
      "35.5.4"));
}

TEST(DpiImportLowering, AnImportDeclaredInTheCompilationUnitIsRegistered) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "import \"DPI-C\" function int unit_add(input int a);\n"
      "module t;\n"
      "  int r;\n"
      "  initial r = unit_add(10);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dpi = f.ctx.GetDpiRuntime();
  ASSERT_NE(dpi, nullptr);
  EXPECT_TRUE(dpi->HasImport("unit_add"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "imported subroutine 'unit_add' is bound to no foreign implementation", 4,
      "35.5.4"));
}

}  // namespace
