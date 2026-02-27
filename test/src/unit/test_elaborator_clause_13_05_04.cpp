// §13.5.4: Argument binding by name

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// named argument call elaborates without error
TEST(ElabA609, NamedArgCallElaborates) {
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

// § list_of_arguments — named arguments elaborate
TEST(ElabA82, NamedArgsElaborate) {
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

}  // namespace
