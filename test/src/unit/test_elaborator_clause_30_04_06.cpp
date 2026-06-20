#include "fixture_elaborator.h"

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
// expansion being applied across the whole list.
TEST(MultiplePathDeclarationElaboration, EveryDestinationInListIsAnEndpoint) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, input b, output x, input y);\n"
      "  specify\n"
      "    (a, b *> x, y) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.6: the expansion to individual paths is symmetric, so every member of
// the source list is also an independent path source and is validated as such.
// Production walks the source list with a loop separate from the destination
// loop, so this exercises that path: the second listed source is an output
// port, which is not a legal path source. A first-element-only check would miss
// it, so the error confirms every source in the list participates in the
// cross-product.
TEST(MultiplePathDeclarationElaboration, EverySourceInListIsAnEndpoint) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, output b, output x, output y);\n"
      "  specify\n"
      "    (a, b *> x, y) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
