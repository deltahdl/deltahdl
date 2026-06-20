#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §16.10: a name that is already a formal argument of a sequence declaration
// cannot be redeclared as a body-scope local variable in an
// assertion_variable_declaration. The elaborator must flag the redeclaration.
TEST(LocalVariableElaboration, FormalArgumentRedeclaredInSequenceBodyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence sub_seq3(lv);\n"
      "    int lv;\n"
      "    @(posedge clk) (a ##1 lv);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.10: the same rule applies to a property declaration — a formal that is
// reintroduced as a body-scope local variable is illegal.
TEST(LocalVariableElaboration, FormalArgumentRedeclaredInPropertyBodyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  property p(lv);\n"
      "    bit lv;\n"
      "    @(posedge clk) lv |-> b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.10: a body-scope local variable whose name does not collide with any
// formal argument is legal, even when the declaration appears alongside
// formal arguments on the port list.
TEST(LocalVariableElaboration, FreshBodyLocalAlongsideFormalElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  sequence s(lv);\n"
      "    int guard;\n"
      "    @(posedge clk) (a, guard = b) ##1 lv;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
