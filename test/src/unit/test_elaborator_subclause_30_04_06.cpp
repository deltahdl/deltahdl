#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(MultiplePathDeclarationElaboration, MixedWidthsInBothLists) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input [3:0] b, input [7:0] c,\n"
      "         output x, output [15:0] y);\n"
      "  specify\n"
      "    (a, b, c *> x, y) = 4;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.6: a multiple module path declaration is equivalent to the full set of
// individual source-to-destination paths. Production realizes this by treating
// every member of the destination list as its own path endpoint, so a non-first
// destination that is not a legal endpoint must still be rejected. Here the
// second listed destination is an input port; if only the first endpoint were
// checked the error would be missed, so this observes the cross-product
// expansion being applied across the whole list. §30.4.6 states the expansion
// and no endpoint rule of its own; the rule that rejects y is §30.4.1's "The
// module path destination shall be a net or variable that is connected to a
// module output port or inout port", so the report carries §30.4.1.
TEST(MultiplePathDeclarationElaboration, EveryDestinationInListIsAnEndpoint) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, input b, output x, input y);\n"
      "  specify\n"
      "    (a, b *> x, y) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "module path destination 'y' must be connected to an output", 3,
      "30.4.1"));
}

// §30.4.6: the expansion to individual paths is symmetric, so every member of
// the source list is also an independent path source and is validated as such.
// Production walks the source list with a loop separate from the destination
// loop, so this exercises that path: the second listed source is an output
// port, which is not a legal path source. A first-element-only check would miss
// it, so the error confirms every source in the list participates in the
// cross-product. As above, the rule that rejects b is §30.4.1's "The module
// path source shall be a net that is connected to a module input port or inout
// port", so the report carries §30.4.1.
TEST(MultiplePathDeclarationElaboration, EverySourceInListIsAnEndpoint) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, output b, output x, output y);\n"
      "  specify\n"
      "    (a, b *> x, y) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "module path source 'b' must be connected to an input", 3, "30.4.1"));
}

// §30.4.6: within a multiple module path the source and destination lists may
// hold a mix of scalars and vectors of any size, because the connection is
// always a full one (a full connection places no width relationship on the two
// ends). Input form: a scalar source paired with a wider vector destination.
// Production accepts because the full-connection width check is skipped for the
// '*>' list form; if this statement were treated as a parallel connection the
// unequal widths would be rejected, so acceptance observes the full-connection
// rule being applied to the multi-path list.
TEST(MultiplePathDeclarationElaboration,
     ScalarSourceToVectorDestinationAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output [7:0] x, output [3:0] y);\n"
      "  specify\n"
      "    (a, b *> x, y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.6: the "any size" allowance is symmetric in width direction. Input
// form: vector sources paired with narrower scalar destinations. A parallel
// connection would reject the width difference; the multi-path '*>' list
// accepts it.
TEST(MultiplePathDeclarationElaboration,
     VectorSourceToScalarDestinationAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, input [3:0] b, output x, output y);\n"
      "  specify\n"
      "    (a, b *> x, y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.6: "of any size" means listed vectors need bear no width relationship
// to each other or across the two lists. Input form: every terminal is a vector
// and no two share a width. The multi-path '*>' list accepts all cross-product
// pairs.
TEST(MultiplePathDeclarationElaboration,
     UnequalVectorWidthsAcrossListsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, input [1:0] b,\n"
      "         output [3:0] x, output [15:0] y);\n"
      "  specify\n"
      "    (a, b *> x, y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
