#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elab1380, VirtualClassStaticFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "virtual class C#(parameter W = 8);\n"
      "  static function logic [W-1:0] encode(input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  logic [7:0] val;\n"
      "  assign val = C#(8)::encode(8'hAB);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab1380, VirtualClassStaticTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "virtual class Printer#(parameter int ID = 0);\n"
      "  static task print();\n"
      "    $display(\"ID=%0d\", ID);\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  initial Printer#(5)::print();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab1380, MultipleStaticMethods) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "virtual class C#(parameter W = 4);\n"
      "  static function logic [W-1:0] encode(input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  static function logic [W-1:0] decode(input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  assign a = C#(4)::encode(4'hF);\n"
      "  assign b = C#(4)::decode(4'hA);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab1380, DifferentSpecializations) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "virtual class C#(parameter W = 8);\n"
      "  static function logic [W-1:0] identity(input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] b;\n"
      "  assign a = C#(4)::identity(4'hC);\n"
      "  assign b = C#(8)::identity(8'hDE);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab1380, TypeParameterElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "virtual class Converter#(parameter type T = int);\n"
      "  static function T identity(input T val);\n"
      "    return val;\n"
      "  endfunction\n"
      "endclass\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elab1380, ParamInForLoopBound) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "virtual class Popcount#(parameter W = 8);\n"
      "  static function int count_ones(input logic [W-1:0] val);\n"
      "    int cnt;\n"
      "    cnt = 0;\n"
      "    for (int i = 0; i < W; i++) begin\n"
      "      if (val[i]) cnt = cnt + 1;\n"
      "    end\n"
      "    return cnt;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial result = Popcount#(8)::count_ones(8'hA5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}
