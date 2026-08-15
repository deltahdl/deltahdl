#include "fixture_parser.h"
#include "helpers_reported_error.h"

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

  // §22.5.1 owns the text-macro usage rule and Preprocessor files the report
  // under it; §5.6.4 only states that a directive's effect ends with the
  // compilation unit.
  EXPECT_TRUE(ReportedError(r2.diags, "undefined macro 'FOO'", 2, "22.5.1"));
}

}  // namespace
