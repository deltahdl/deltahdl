#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(OperatorPreprocessor, SingleCharOperatorPassesThrough) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  assign a = b + c;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OperatorPreprocessor, DoubleCharOperatorPassesThrough) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = (b == 8'd0);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OperatorPreprocessor, TripleCharOperatorPassesThrough) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = (b === 8'd0);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OperatorPreprocessor, UnaryOperatorPassesThrough) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = ~b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OperatorPreprocessor, BinaryOperatorPassesThrough) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  assign a = b & c;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OperatorPreprocessor, ConditionalOperatorPassesThrough) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, c;\n"
      "  assign a = sel ? b : c;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OperatorPreprocessor, OperatorsInMacroExpansion) {
  PreprocFixture f;
  Preprocess(
      "`define ADD(a, b) ((a) + (b))\n"
      "module t;\n"
      "  logic [7:0] x, y, z;\n"
      "  assign x = `ADD(y, z);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OperatorPreprocessor, MixedOperatorsPassThrough) {
  PreprocFixture f;
  Preprocess(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  assign a = (b + c) & ~d;\n"
      "  assign d = b ? c : 8'd0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
