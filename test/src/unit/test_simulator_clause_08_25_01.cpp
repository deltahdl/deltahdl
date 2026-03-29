#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(ParameterizedScopeResolutionSim, ExplicitDefaultReturnsClassParamDefault) {
  EXPECT_EQ(RunAndGet(
      "class C #(parameter int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = C#()::p;\n"
      "endmodule\n", "result"), 1u);
}

TEST(ParameterizedScopeResolutionSim, ExplicitDefaultReturnsLocalParamValue) {
  EXPECT_EQ(RunAndGet(
      "class C #(parameter int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = C#()::q;\n"
      "endmodule\n", "result"), 5u);
}

TEST(ParameterizedScopeResolutionSim, BothClassAndLocalParamsReadable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(parameter int p = 10);\n"
      "  parameter int q = 20;\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#()::p;\n"
      "    b = C#()::q;\n"
      "  end\n"
      "endmodule\n", f);
  LowerRunAndCheck(f, design, {{"a", 10u}, {"b", 20u}});
}

TEST(ParameterizedScopeResolutionSim, OutOfBlockMethodAccessesParam) {
  EXPECT_EQ(RunAndGet(
      "class C #(parameter int p = 1);\n"
      "  extern static function int f();\n"
      "endclass\n"
      "function int C::f();\n"
      "  return p;\n"
      "endfunction\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = C#()::f();\n"
      "endmodule\n", "result"), 1u);
}

TEST(ParameterizedScopeResolutionSim, SpecificSpecializationMethodUsesOverride) {
  EXPECT_EQ(RunAndGet(
      "virtual class C #(parameter int W = 8);\n"
      "  static function int get_w;\n"
      "    get_w = W;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = C#(42)::get_w();\n"
      "endmodule\n", "result"), 42u);
}

TEST(ParameterizedScopeResolutionSim, TwoSpecializationsReturnDifferentValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class C #(parameter int W = 8);\n"
      "  static function int get_w;\n"
      "    get_w = W;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#(3)::get_w();\n"
      "    b = C#(7)::get_w();\n"
      "  end\n"
      "endmodule\n", f);
  LowerRunAndCheck(f, design, {{"a", 3u}, {"b", 7u}});
}

}  // namespace
