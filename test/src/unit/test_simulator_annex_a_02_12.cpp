#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(LetSim, NoPortLetExpandsToRhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  let answer = 8'd42;\n"
      "  initial x = answer;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

TEST(LetSim, PositionalLiteralActualsSubstituted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  let sum(a, b) = a + b;\n"
      "  initial x = sum(8'd5, 8'd9);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 14u}});
}

TEST(LetSim, CompoundExpressionActualsSubstituted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y, z;\n"
      "  let sum(a, b) = a + b;\n"
      "  initial begin\n"
      "    y = 8'd2;\n"
      "    z = 8'd4;\n"
      "    x = sum(y + 8'd1, z);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}});
}

TEST(LetSim, TypedFormalNarrowsActualToDataTypeWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  let low(logic [3:0] v) = v;\n"
      "  initial x = low(8'hAB);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 11u}});
}

TEST(LetSim, UntypedFormalPassesActualThrough) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  let same(untyped a) = a;\n"
      "  initial x = same(8'hC8);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 200u}});
}

TEST(LetSim, PortDefaultUsedWhenActualOmitted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  let scaled(int d = 5) = d * 2;\n"
      "  initial x = scaled();\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 10u}});
}

TEST(LetSim, NamedActualsBindByName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
      "  initial x = mux(.sel(1'b1), .d0(8'd10), .d1(8'd20));\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 20u}});
}

TEST(LetSim, FormalOfATypeReferenceTakesTheReferencedType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  let f(type(x) a) = a + 1;\n"
      "  int r;\n"
      "  initial r = f(-5);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 0xFFFFFFFCu}});
}

}  // namespace
