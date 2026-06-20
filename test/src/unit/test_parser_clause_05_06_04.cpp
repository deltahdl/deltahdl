#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, DirectivePersistsAcrossModules) {
  auto r = ParseWithPreprocessor(
      "`define WIDTH 8\n"
      "module m1;\n"
      "  localparam W1 = `WIDTH;\n"
      "endmodule\n"
      "module m2;\n"
      "  localparam W2 = `WIDTH;\n"
      "endmodule\n"
      "module m3;\n"
      "  localparam W3 = `WIDTH;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 3u);
}

TEST(CompilerDirectiveParsing, DirectiveTakesEffectBeforeNextLineParses) {
  auto r = ParseWithPreprocessor(
      "`define WIDTH 8\n"
      "module m;\n"
      "  logic [`WIDTH-1:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(CompilerDirectiveParsing, ImmediateEffectVisibleInLocalparam) {
  auto r = ParseWithPreprocessor(
      "`define VAL 42\n"
      "localparam P = `VAL;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "P");
}

TEST(CompilerDirectiveParsing, DirectiveDoesNotAffectOtherCU) {
  auto r1 = ParseWithPreprocessor(
      "`define FOO 1\n"
      "module m1;\n"
      "  localparam X = `FOO;\n"
      "endmodule\n");
  EXPECT_FALSE(r1.has_errors);

  auto r2 = ParseWithPreprocessor(
      "module m2;\n"
      "  localparam Y = `FOO;\n"
      "endmodule\n");

  EXPECT_TRUE(r2.has_errors);
}

}  // namespace
