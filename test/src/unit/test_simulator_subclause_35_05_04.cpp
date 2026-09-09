#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
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

// §35.5.4 declares an imported subroutine where the source writes it, and §35.6
// has a call to one written exactly as a call to a native subroutine. What
// joins the two is the registry: a call reaches its declaration through it, and
// a design's own declarations reached it by no route at all -- the registry was
// built by whichever unit test constructed one, so every rule clause 35 holds
// of was held of a registry the simulator never consulted, and `x = f(a);`
// against an imported `f` yielded a one-bit zero.
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

// §35.5.1.2 reads each formal's direction to decide which way its value
// crosses, and §35.6.1 copies the written ones back into the actuals, so the
// directions travel with the declaration. A lowering that registered names
// alone satisfies the case above and loses every write-back.
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

// §35.5.6 admits "Packed arrays, structs, and unions composed of types bit and
// logic" as formal types and names no width limit, and DataTypeKind says only
// `bit` for `bit [127:0]`. So the width the declaration wrote has to travel
// with the formal: without it the crossing sizes that formal by its kind and
// hands the foreign side one bit of the design's 128.
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
  // A formal whose type states its own width records none: the kind is the one
  // answer about how wide an `int` is, and a second one beside it could differ
  // from it.
  EXPECT_EQ(import->args[1].width, 0U);
}

// §35.4 makes the declaration a reference to a global symbol the foreign side
// defines and §35.5.4 leaves the binding to the tool. Nothing supplies one
// here, so the call reaches no implementation, and what it must not do is
// answer: a zero the design reads as data cannot be told from a foreign
// function that returned zero.
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

}  // namespace
