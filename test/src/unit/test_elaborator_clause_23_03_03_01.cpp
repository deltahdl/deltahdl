
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Section 23.3.3.1 leaves coercion optional ("may be coerced") but mandates a
// warning when a mis-directed port is not coerced. This implementation never
// coerces, so every coercion-eligible port must produce the SHALL warning while
// remaining a non-error (elaboration still succeeds).

// C2, input branch: an input port driven inside the instantiated module is used
// as an output/inout, so the warning is issued (and it is not an error).
TEST(PortCoercionElaboration, InputDrivenInsideModuleWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

// C2, output branch: an output port whose external connection is also driven
// from outside is used as an input/inout, so the warning is issued.
TEST(PortCoercionElaboration, OutputWithExternalDriverWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(output wire b);\n"
      "  assign b = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire y;\n"
      "  assign y = 1'b0;\n"
      "  child u(.b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

// Negative guard: ports used in their declared direction need no coercion, so
// no warning is emitted.
TEST(PortCoercionElaboration, CorrectDirectionsNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x, y;\n"
      "  child u(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// Negative guard: an already-inout port is bidirectional, so driving it inside
// the module is legal and needs no coercion warning even though the same usage
// on an input port would warn.
TEST(PortCoercionElaboration, InoutPortNeedsNoCoercion) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire data);\n"
      "  assign data = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire bus;\n"
      "  assign bus = 1'b0;\n"
      "  child u(.data(bus));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
