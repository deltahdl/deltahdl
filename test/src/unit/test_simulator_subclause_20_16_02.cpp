#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PlaArrayLogicType, LogicPlanesApplyAcrossAllTypesAndFormats) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:1] saa, soa, snda, snra;\n"
      "  logic [1:1] aaa, aoa, anda, anra;\n"
      "  logic [1:1] sap, sop, sndp, snrp;\n"
      "  logic [1:1] aap, aop, andp, anrp;\n"
      "  initial begin\n"
      "    mem[1] = 2'b11;\n"
      "    in = 2'b10;\n"
      "    $sync$and$array(mem, in, saa);\n"
      "    $sync$or$array(mem, in, soa);\n"
      "    $sync$nand$array(mem, in, snda);\n"
      "    $sync$nor$array(mem, in, snra);\n"
      "    $async$and$array(mem, in, aaa);\n"
      "    $async$or$array(mem, in, aoa);\n"
      "    $async$nand$array(mem, in, anda);\n"
      "    $async$nor$array(mem, in, anra);\n"
      "    $sync$and$plane(mem, in, sap);\n"
      "    $sync$or$plane(mem, in, sop);\n"
      "    $sync$nand$plane(mem, in, sndp);\n"
      "    $sync$nor$plane(mem, in, snrp);\n"
      "    $async$and$plane(mem, in, aap);\n"
      "    $async$or$plane(mem, in, aop);\n"
      "    $async$nand$plane(mem, in, andp);\n"
      "    $async$nor$plane(mem, in, anrp);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  const char* and_outs[] = {"saa", "aaa", "sap", "aap"};
  const char* or_outs[] = {"soa", "aoa", "sop", "aop"};
  const char* nand_outs[] = {"snda", "anda", "sndp", "andp"};
  const char* nor_outs[] = {"snra", "anra", "snrp", "anrp"};
  for (const char* name : and_outs) {
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->value.ToUint64(), 0u) << name;
  }
  for (const char* name : or_outs) {
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->value.ToUint64(), 1u) << name;
  }
  for (const char* name : nand_outs) {
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->value.ToUint64(), 1u) << name;
  }
  for (const char* name : nor_outs) {
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->value.ToUint64(), 0u) << name;
  }
}

TEST(PlaArrayLogicType, NandPlaneAppliesNandInPlaneFormat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:1];\n"
      "  logic [1:1] out_plane, out_array;\n"
      "  initial begin\n"
      "    mem[1] = 2'b00;\n"
      "    in = 2'b11;\n"
      "    $sync$nand$plane(mem, in, out_plane);\n"
      "    $sync$nand$array(mem, in, out_array);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* out_plane = f.ctx.FindVariable("out_plane");
  auto* out_array = f.ctx.FindVariable("out_array");
  ASSERT_NE(out_plane, nullptr);
  ASSERT_NE(out_array, nullptr);
  EXPECT_EQ(out_plane->value.ToUint64(), 1u);
  EXPECT_EQ(out_array->value.ToUint64(), 0u);
}

TEST(PlaArrayLogicType, LogicFunctionAppliesPerWordOverConcatenatedTerms) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a1, a2;\n"
      "  logic b1, b2;\n"
      "  logic [1:2] mem [1:2];\n"
      "  initial begin\n"
      "    mem[1] = 2'b11;\n"
      "    mem[2] = 2'b10;\n"
      "    a1 = 1; a2 = 0;\n"
      "    $sync$nand$array(mem, {a1,a2}, {b1,b2});\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* b1 = f.ctx.FindVariable("b1");
  auto* b2 = f.ctx.FindVariable("b2");
  ASSERT_NE(b1, nullptr);
  ASSERT_NE(b2, nullptr);
  EXPECT_EQ(b1->value.ToUint64(), 1u);
  EXPECT_EQ(b2->value.ToUint64(), 0u);
}

TEST(PlaArrayLogicType, AsyncNorPlaneReevaluatesNorInPlaneFormat) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    mem[1] = 2'b00;\n"
                           "    in = 2'b00;\n"
                           "    $async$nor$plane(mem, in, out);\n"
                           "    #1 in = 2'b11;\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 1u);
}

}  // namespace
