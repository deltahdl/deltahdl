#include "fixture_parser.h"

using namespace delta;

namespace {

// §5.6.4: "The directive shall remain in effect for the rest of the
// compilation unit (see 3.12.1) unless a different compiler directive
// specifies otherwise."  A `define remains visible across all subsequent
// modules within the same compilation unit.
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

// §5.6.4: "The compiler behavior dictated by a compiler directive shall take
// effect as soon as the compiler reads the directive."  The `define on the
// preceding line must already be in effect when the parser reaches the use.
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

// §5.6.4: A compiler directive whose effect appears immediately after a
// `define has been read parses without error — the macro has already been
// installed.
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

// §5.6.4: "A compiler directive shall not affect other compilation units."
// A `define from one parse must not leak into a separate parse.
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
