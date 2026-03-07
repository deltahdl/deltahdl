#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

// §10.10: Empty unpacked array concatenation elaborates without errors.
TEST(ElabCh10j, EmptyUnpackedArrayConcatElab) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = {};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.10: Basic unpacked array concatenation elaborates.
TEST(ElabCh10j, UnpackedArrayConcatElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[3];\n"
      "  initial A = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.10: Array items in unpacked array concatenation elaborate.
TEST(ElabCh10j, ArrayItemExpansionElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[2], B[2], C[4];\n"
      "  initial C = {A, B};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.10: Mixed scalars and arrays in unpacked array concatenation.
TEST(ElabCh10j, MixedScalarArrayElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[2], B[3];\n"
      "  initial B = {A, 5};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.10: Queue target with unpacked array concatenation.
TEST(ElabCh10j, QueueConcatElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.10.2: Concatenation braces disambiguate based on target type.
TEST(ElabCh10j, ConcatBracesDisambiguateByTarget) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte B;\n"
      "  byte BA[2];\n"
      "  initial begin\n"
      "    B = {4'h6, 4'hf};\n"
      "    BA = {4'h6, 4'hf};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

}  // namespace
