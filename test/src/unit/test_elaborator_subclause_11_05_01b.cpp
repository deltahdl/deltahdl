#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

// §11.5.2 sends a select of an array element to §11.5.1 for judgement: "Once
// selected, bit-selects and part-selects shall be addressed in the same manner
// as net and variable bit-selects and part-selects (see 11.5.1)." §11.5.1 then
// bars this operand: "A bit-select or part-select of a scalar, or of a real
// variable or real parameter, shall be illegal." `arr[i]` selects one real
// element, and `[0]` selects a bit out of that real, so the source is illegal.
//
// This fails while CheckRealSelectNode in
// src/elaborator/elaborator_validate.cpp opens with ExprIdent(e->base), which
// returns nothing for `arr[i][0]` because the base of the outer select is
// another select rather than an identifier. The check then judges nothing and
// the run reports no error at all.
TEST(RealSelect, BitSelectOfARealArrayElementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial v = arr[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "11.5.1"));
}

// The same operand written as a part-select. §11.5.1 names a bit-select and a
// part-select as two constructs, and `arr[i][3:0]` is the second of them.
// CheckRealSelectNode in src/elaborator/elaborator_validate.cpp chooses between
// the two messages on fields of the select node -- `index_end`,
// `is_part_select_plus` and `is_part_select_minus` -- that are separate from
// the `base` field a fix has to walk to reach the element. So a fix that
// reaches the real element could still name the wrong construct, and this case
// fails when it does as well as when no report is made.
TEST(RealSelect, PartSelectOfARealArrayElementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial v = arr[i][3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real variable is illegal", 5,
                            "11.5.1"));
}

// The same §11.5.1 breach written in the statement-target position, which
// CheckRealSelectStmt in src/elaborator/elaborator_validate.cpp reaches through
// `s->lhs` by a different call into CheckRealSelect than the one that reaches
// the source position through `s->rhs`. A fix applied to the source position
// alone therefore leaves this select unjudged, and this case fails when it
// does.
TEST(RealSelect, BitSelectOfARealArrayElementAsATargetIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial arr[i][0] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 5,
                            "11.5.1"));
}

// §11.5.1's other alternative, reached by the same §11.5.2 route: "A bit-select
// or part-select of a scalar, or of a real variable or real parameter, shall be
// illegal." `s` is declared `logic s[4]`, so `s[i]` selects one scalar element
// and `[0]` selects a bit out of that scalar.
//
// This fails while CheckScalarSelectNode in
// src/elaborator/elaborator_validate.cpp opens with ExprIdent(e->base) and
// stops when the answer is empty, which it is for a base that is itself a
// select. A fix that walks the chain for reals alone leaves this case silent.
TEST(SelectElaboration, BitSelectOfAScalarArrayElementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic s[4];\n"
      "  logic v;\n"
      "  int i;\n"
      "  initial v = s[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            5, "11.5.1"));
}

// The control that stops a fix from rejecting the case §11.5.2 exists to
// permit. §11.5.2 reads: "To express bit-selects or part-selects of array
// elements, the desired word shall first be selected by supplying an address
// for each dimension." `mem[i]` is that one address and selects the word, and
// `[0]` then bit-selects a vector element, which §11.5.1 bars only for a scalar
// or a real. This fails when a fix reports every second address rather than
// reading the element's type.
TEST(SelectElaboration, BitSelectOfAPackedArrayElementIsStillLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] mem[4];\n"
      "  logic v;\n"
      "  int i;\n"
      "  initial v = mem[i][0];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// This pins that "an address for each dimension" is counted against the
// declaration rather than assumed to be one. `mem` is declared with two
// unpacked dimensions, so `mem[i][i]` selects the word and `[0]` is the first
// address past the declaration's dimensions. This fails when a fix treats the
// second address as the bit-select whatever the declaration says, which rejects
// a legal element select of a two-dimensional array.
TEST(SelectElaboration, BitSelectOfATwoDimensionalArrayElementIsStillLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] mem[4][4];\n"
      "  logic v;\n"
      "  int i;\n"
      "  initial v = mem[i][i][0];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}
