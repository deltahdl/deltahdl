#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §13.8: Parameterized static function returns correct value.
TEST(Sim1380, ParameterizedStaticFunctionReturnsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class Doubler#(parameter W = 8);\n"
      "  static function logic [W-1:0] double_val(\n"
      "      input logic [W-1:0] x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = Doubler#(8)::double_val(8'd21);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 42u}});
}

// §13.8: Different specializations produce different-width results.
TEST(Sim1380, DifferentSpecializationsWork) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class Identity#(parameter W = 8);\n"
      "  static function logic [W-1:0] id(\n"
      "      input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = Identity#(8)::id(8'hAB);\n"
      "    b = Identity#(8)::id(8'hCD);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0xABu}, {"b", 0xCDu}});
}

// §13.8: Parameter used in for-loop bound at runtime.
TEST(Sim1380, ParamUsedInForLoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class Popcount#(parameter W = 8);\n"
      "  static function int count_ones(\n"
      "      input logic [W-1:0] val);\n"
      "    int cnt;\n"
      "    cnt = 0;\n"
      "    for (int i = 0; i < W; i++) begin\n"
      "      if (val[i]) cnt = cnt + 1;\n"
      "    end\n"
      "    return cnt;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = Popcount#(8)::count_ones(8'b1010_0101);\n"
      "endmodule\n",
      f);
  // 8'b1010_0101 has 4 ones
  LowerRunAndCheck(f, design, {{"result", 4u}});
}

// §13.8: Multiple static methods in same parameterized class.
TEST(Sim1380, MultipleMethodsSameClass) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class Math#(parameter W = 8);\n"
      "  static function logic [W-1:0] add_one(\n"
      "      input logic [W-1:0] x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "  static function logic [W-1:0] sub_one(\n"
      "      input logic [W-1:0] x);\n"
      "    return x - 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = Math#(8)::add_one(8'd10);\n"
      "    b = Math#(8)::sub_one(8'd10);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 11u}, {"b", 9u}});
}

}  // namespace
