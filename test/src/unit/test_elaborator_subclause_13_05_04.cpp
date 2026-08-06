#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SubroutineCallElaborationSyntax, NamedArgCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = add(.b(2), .a(1));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArgumentBindingElaboration, UnknownNamedArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  int x;\n"
      "  initial x = add(.c(1), .a(2));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ArgumentBindingElaboration, MixedPositionalNamedOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int add3(int a, int b, int c);\n"
      "    return a + b + c;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = add3(1, .c(3), .b(2));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArgumentBindingElaboration, MissingRequiredNamedArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  int x;\n"
      "  initial x = add(.a(1));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ArgumentBindingElaboration, OmitDefaultedArgWithNamedBindingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int scale(int val, int factor = 3);\n"
      "    return val * factor;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = scale(.val(7));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
