#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(OperatorParsing, UnaryModulePathNot) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (!a) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathBitwiseNot) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (~a) (a => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathNeq) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a != b) (a => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathLogicalOr) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a || b) (a => y) = 4;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathXnorAlt) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ~^ b) (a => y) = 9;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathEq) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a == b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathNotEq) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a != b) (a => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathLogicalAnd) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a && b) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathBitwiseAnd) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a & b) (a => y) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathBitwiseOr) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a | b) (a => y) = 6;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathXor) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ^ b) (a => y) = 7;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathXnor) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ^~ b) (a => y) = 8;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathReductionAnd) {
  auto r = Parse(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (&a) (a[0] => y) = 11;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathReductionOr) {
  auto r = Parse(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (|a) (a[0] => y) = 12;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathReductionXor) {
  auto r = Parse(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (^a) (a[0] => y) = 13;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathReductionNand) {
  auto r = Parse(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (~&a) (a[0] => y) = 14;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathReductionNor) {
  auto r = Parse(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (~|a) (a[0] => y) = 15;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathReductionXnor) {
  auto r = Parse(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (~^a) (a[0] => y) = 16;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, ModulePathConcat) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if ({a, b}) (a => y) = 17;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, ModulePathReplication) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if ({2{a}}) (a => y) = 18;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, ModulePathTernary) {
  auto r = Parse(
      "module m(input a, input b, input c, output y);\n"
      "  specify\n"
      "    if (a ? b : c) (a => y) = 19;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- Operand classes ---

TEST(OperatorParsing, ModulePathOperandSpecparam) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    specparam SP = 1;\n"
      "    if (SP) (a => y) = 20;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, ModulePathOperandLocalNet) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  wire en;\n"
      "  specify\n"
      "    if (en) (a => y) = 21;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, ModulePathOperandConstantNumber) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (1'b1) (a => y) = 22;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, ModulePathOperandBitSelect) {
  auto r = Parse(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (a[0]) (a[0] => y) = 23;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, ModulePathOperandPartSelect) {
  auto r = Parse(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (a[1:0]) (a[0] => y) = 24;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
