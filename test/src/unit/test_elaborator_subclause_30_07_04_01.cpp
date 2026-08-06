#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SpecifyBlockDeclElaboration, PulsestyleOnModulePathOutputIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "    pulsestyle_onevent o;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(f.has_errors);
}

// The error is specific to a pulsestyle output that appears *after* the module
// path declaration. A pulsestyle declaration that precedes the path on the same
// output is legal, so order is what discriminates the rule.
TEST(SpecifyBlockDeclElaboration, PulsestyleBeforeModulePathIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    pulsestyle_onevent o;\n"
      "    (a => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The error rule applies to every output in a multi-output pulsestyle
// declaration, not just the first one listed. Here the conflicting output (o,
// already a module path destination) appears second in the list, so the per
// output scan must still flag it.
TEST(SpecifyBlockDeclElaboration,
     ConflictAmongMultiplePulsestyleOutputsIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o, output p);\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "    pulsestyle_onevent p, o;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
