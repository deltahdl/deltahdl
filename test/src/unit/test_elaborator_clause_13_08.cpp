#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParameterizedSubroutineElaboration, VirtualClassStaticFunctionElaborates) {
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

TEST(ParameterizedSubroutineElaboration, VirtualClassStaticTaskElaborates) {
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

TEST(ParameterizedSubroutineElaboration, MultipleStaticMethods) {
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

TEST(ParameterizedSubroutineElaboration, DifferentSpecializations) {
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

TEST(ParameterizedSubroutineElaboration, TypeParameterElaborates) {
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

TEST(ParameterizedSubroutineElaboration, ParamInForLoopBound) {
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

TEST(ParameterizedSubroutineElaboration, DependentDefaultParamElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "virtual class C#(parameter DECODE_W = 8,\n"
      "                 parameter ENCODE_W = $clog2(DECODE_W));\n"
      "  static function logic [ENCODE_W-1:0] ENCODER_f(\n"
      "      input logic [DECODE_W-1:0] DecodeIn);\n"
      "    ENCODER_f = '0;\n"
      "    for (int i = 0; i < DECODE_W; i++) begin\n"
      "      if (DecodeIn[i]) begin\n"
      "        ENCODER_f = i[ENCODE_W-1:0];\n"
      "      end\n"
      "    end\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  logic [7:0] encoder_in;\n"
      "  logic [2:0] encoder_out;\n"
      "  assign encoder_out = C#(8)::ENCODER_f(encoder_in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParameterizedSubroutineElaboration, NonVirtualClassElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C#(parameter W = 8);\n"
      "  static function logic [W-1:0] identity(input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  logic [7:0] val;\n"
      "  assign val = C#(8)::identity(8'hAB);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
