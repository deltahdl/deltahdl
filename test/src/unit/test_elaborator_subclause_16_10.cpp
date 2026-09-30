#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is a formal argument and cannot be redeclared", 3,
                            "16.10"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is a formal argument and cannot be redeclared", 3,
                            "16.10"));
}

// §16.10: a local variable formal argument (declared with the `local` keyword,
// see §16.8.2) is itself a "local variable"; redeclaring its name as a
// body-scope assertion_variable_declaration in the same sequence is the same
// illegality as for a plain formal. The elaborator must flag the collision.
TEST(LocalVariableElaboration, LocalFormalArgumentRedeclaredInBodyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  sequence s(local input int lv);\n"
      "    int lv;\n"
      "    @(posedge clk) (a, b) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is a formal argument and cannot be redeclared", 3,
                            "16.10"));
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

// §16.10: the local variables declared in a sequence are not visible where the
// sequence is instantiated. The clause's own example: `seq1` instantiates
// `sub_seq1` and then reads `v1`, which only `sub_seq1` declares, so the read
// resolves to nothing and names the local it cannot reach.
TEST(LocalVariableElaboration, InstantiatedSequencesLocalIsNotVisible) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  bit a, b, c, do1;\n"
      "  int data_in, data_out;\n"
      "  sequence sub_seq1;\n"
      "    int v1;\n"
      "    (a ##1 !a, v1 = data_in) ##1 !b[*0:$] ##1 b && (data_out == v1);\n"
      "  endsequence\n"
      "  sequence seq1;\n"
      "    c ##1 sub_seq1 ##1 (do1 == v1);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'v1' is a local variable of sequence 'sub_seq1' "
                            "and is not visible outside its body",
                            10, "16.10"));
}

// §16.10 names the local only where the reading text instantiates the
// declaration holding it. Here the assertion instantiates `s2` alone, so its
// read of `v`, which only `s1` declares, is an unresolved name (§23.9) and
// not an invisible local.
TEST(LocalVariableElaboration, LocalOfASequenceNotInstantiatedIsUnresolved) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic clk, a);\n"
      "  sequence s1; int v; (a, v = 1) ##1 (v == 1); endsequence\n"
      "  sequence s2(x); x; endsequence\n"
      "  assert property (@(posedge clk) s2(a) ##1 v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'v'", 4,
                            "23.9"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "is a local variable", 4, "16.10"));
}

}  // namespace
