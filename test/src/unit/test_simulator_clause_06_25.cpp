#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ParameterizedTypeSim, TypeParamAssignAndRead) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(type T = int);\n"
      "  typedef T my_type;\n"
      "endclass\n"
      "module top;\n"
      "  C#(logic [7:0])::my_type x;\n"
      "  initial x = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
  EXPECT_EQ(var->value.width, 8u);
}

TEST(ParameterizedTypeSim, ValueParamWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class bus_def #(parameter WIDTH = 8);\n"
      "  typedef logic [WIDTH-1:0] data_t;\n"
      "endclass\n"
      "module top;\n"
      "  bus_def#(16)::data_t x;\n"
      "  initial x = 16'hCAFE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
  EXPECT_EQ(var->value.width, 16u);
}

TEST(ParameterizedTypeSim, DistinctSpecializationsHoldIndependentValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class bus_def #(parameter WIDTH = 8);\n"
      "  typedef logic [WIDTH-1:0] data_t;\n"
      "endclass\n"
      "module top;\n"
      "  bus_def#(8)::data_t narrow;\n"
      "  bus_def#(16)::data_t wide;\n"
      "  initial begin\n"
      "    narrow = 8'hFF;\n"
      "    wide = 16'h1234;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v_narrow = f.ctx.FindVariable("narrow");
  auto* v_wide = f.ctx.FindVariable("wide");
  ASSERT_NE(v_narrow, nullptr);
  ASSERT_NE(v_wide, nullptr);
  EXPECT_EQ(v_narrow->value.ToUint64(), 0xFFu);
  EXPECT_EQ(v_narrow->value.width, 8u);
  EXPECT_EQ(v_wide->value.ToUint64(), 0x1234u);
  EXPECT_EQ(v_wide->value.width, 16u);
}

}  // namespace
