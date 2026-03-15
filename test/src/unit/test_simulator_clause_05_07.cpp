#include <cstring>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

static bool LowerRunAndFindIR(SimFixture& f, RtlirDesign* design,
                              Variable*& vi_out, Variable*& vr_out) {
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  vi_out = f.ctx.FindVariable("i");
  vr_out = f.ctx.FindVariable("r");
  EXPECT_NE(vi_out, nullptr);
  EXPECT_NE(vr_out, nullptr);
  return vi_out && vr_out;
}

TEST(NumberLiteralSim, NumberBothFormsCoexist) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] i;\n"
      "  real r;\n"
      "  initial begin\n"
      "    i = 42;\n"
      "    r = 3.14;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(design, nullptr);
  if (!design) return;
  Variable* vi = nullptr;
  Variable* vr = nullptr;
  if (!LowerRunAndFindIR(f, design, vi, vr)) return;
  EXPECT_EQ(vi->value.ToUint64(), 42u);
  double d = 0.0;
  uint64_t bits = vr->value.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_DOUBLE_EQ(d, 3.14);
}

TEST(NumberLiteralSim, NumberRealFixedPoint) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 42.5;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 42.5);
}

TEST(NumberLiteralSim, NumberRealScientific) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 5.0e3;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 5000.0);
}

TEST(NumberLiteralSim, NumberMixedInExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] i;\n"
      "  real r;\n"
      "  initial begin\n"
      "    i = 10 + 20;\n"
      "    r = 1.5 + 2.5;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(design, nullptr);
  if (!design) return;
  Variable* vi = nullptr;
  Variable* vr = nullptr;
  if (!LowerRunAndFindIR(f, design, vi, vr)) return;
  EXPECT_EQ(vi->value.ToUint64(), 30u);
  double d = 0.0;
  uint64_t bits = vr->value.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_DOUBLE_EQ(d, 4.0);
}

