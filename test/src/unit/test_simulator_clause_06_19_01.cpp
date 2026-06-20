#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(TypedefEnumSimulation, NamedEnumTypeVarAssignAndRead) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {NO, YES} boolean;\n"
      "  boolean flag;\n"
      "  integer result;\n"
      "  initial begin\n"
      "    flag = YES;\n"
      "    result = flag;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(TypedefEnumSimulation, NamedEnumTypeReusedForMultipleVars) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {OFF, ON} switch_t;\n"
      "  switch_t a;\n"
      "  switch_t b;\n"
      "  integer ra;\n"
      "  integer rb;\n"
      "  initial begin\n"
      "    a = OFF;\n"
      "    b = ON;\n"
      "    ra = a;\n"
      "    rb = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* ra = f.ctx.FindVariable("ra");
  auto* rb = f.ctx.FindVariable("rb");
  ASSERT_NE(ra, nullptr);
  ASSERT_NE(rb, nullptr);
  EXPECT_EQ(ra->value.ToUint64(), 0u);
  EXPECT_EQ(rb->value.ToUint64(), 1u);
}

}  // namespace
