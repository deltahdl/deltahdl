#include "fixture_elaborator.h"

namespace {

TEST(ConfigLocalparamLiteral, NonLiteralLocalparamRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam X = 1 + 2;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigLocalparamLiteral, IdentifierLocalparamRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam X = a;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigLocalparamLiteral, IntegerLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam X = 8;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigLocalparamLiteral, StringLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam S = \"name\";\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, HierIdentInExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.WIDTH + 7));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigParamOverride, HierIdentAloneAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.WIDTH));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, NonHierIdentInExpressionAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(WIDTH + 7));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, IndexUsingUnknownIdentifierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[i]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigParamOverride, IndexUsingLiteralAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[2]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, IndexUsingConfigLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam IDX = 0;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[IDX]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, HierRefThroughArrayOfInstancesRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.arr[0].WIDTH));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigParamOverride, UserFunctionCallRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(my_func(8)));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigParamOverride, SystemFunctionCallAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W($clog2(8)));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

}
