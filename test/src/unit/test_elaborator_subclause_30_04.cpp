#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §30.4: "Module paths can connect any combination of vectors and scalars." A
// full connection (*>) from a scalar source to an 8-bit vector destination is
// legal even though source and destination widths differ; the equal-width
// requirement applies only to parallel connections, not full connections.
TEST(ModulePathDeclElaboration, FullConnectionMixesScalarSourceAndVectorDest) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input s, output [7:0] q);\n"
      "  specify\n"
      "    (s *> q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4: "Module paths can connect any combination of vectors and scalars." A
// full connection (*>) between two equal-width vectors is legal; the vector-to-
// vector combination elaborates without a width diagnostic.
TEST(ModulePathDeclElaboration, FullConnectionVectorSourceToVectorDest) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [7:0] q);\n"
      "  specify\n"
      "    (a *> q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4: "Module paths can connect any combination of vectors and scalars." The
// reverse-mismatch combination -- a wider vector source driving a scalar
// destination through a full connection (*>) -- is legal, because the equal-
// width rule is confined to parallel connections.
TEST(ModulePathDeclElaboration, FullConnectionVectorSourceToScalarDest) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output q);\n"
      "  specify\n"
      "    (a *> q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4: "Module paths can connect any combination of vectors and scalars." The
// scalar-to-scalar combination -- the simplest full connection (*>) -- also
// elaborates cleanly, completing the set of source/destination shape pairings.
TEST(ModulePathDeclElaboration, FullConnectionScalarSourceToScalarDest) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output q);\n"
      "  specify\n"
      "    (a *> q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4 (Figure 30-1): "More than one source ... may have a module path to the
// same destination, and different delays may be specified for each input to
// output path." Two sources targeting the same destination with distinct delays
// elaborate cleanly.
TEST(ModulePathDeclElaboration, MultipleSourcesToSameDestination) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output q);\n"
      "  specify\n"
      "    (a => q) = 10;\n"
      "    (b => q) = 12;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
