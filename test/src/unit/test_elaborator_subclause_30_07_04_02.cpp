#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The error is specifically about source order: a showcancelled declaration
// is only illegal once the output has *already* appeared in a module path
// declaration. Listing it before the path leaves it legal, so this pins the
// order sensitivity (and exercises the no-conflict branch of the check).
TEST(SpecifyBlockDeclElaboration, ShowcancelledBeforeModulePathIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    showcancelled o;\n"
      "    (a => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyBlockDeclElaboration, ShowcancelledAfterModulePathIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o);\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "    showcancelled o;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "showcancelled declaration for 'o' conflicts with a "
                    "module path that drives the same output",
                    4, "30.7.4.2"));
}

// The error applies to any output named in the declaration, not just the
// first: here the conflicting output is the second entry in the list, so a
// check that only inspected the head of the list would miss it.
TEST(SpecifyBlockDeclElaboration,
     ConflictAmongMultipleShowcancelledOutputsIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output o, output p);\n"
      "  specify\n"
      "    (a => o) = 5;\n"
      "    showcancelled p, o;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "showcancelled declaration for 'o' conflicts with a "
                    "module path that drives the same output",
                    4, "30.7.4.2"));
}

}  // namespace
