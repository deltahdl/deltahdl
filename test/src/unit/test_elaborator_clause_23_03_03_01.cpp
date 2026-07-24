
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

// C2, input branch, vector data type: §23.2.2.3 admits a packed (multi-bit)
// port. A vector input driven internally is used as an output exactly as a
// scalar one is, so the coercion warning still fires — covering the vector
// operand form the scalar test above does not.
TEST(PortCoercionElaboration, VectorInputDrivenInsideModuleWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input wire [7:0] a);\n"
      "  assign a = 8'hFF;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

// C2, output branch, ordered connection: §23.3 (Syntax 23-6) lets the port list
// be positional instead of named. An externally driven output reached through
// an ordered connection is still used as an input, so the warning fires —
// covering the positional syntactic position the named tests above do not.
TEST(PortCoercionElaboration, PositionalConnectionOutputWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(output wire b);\n"
      "  assign b = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire y;\n"
      "  assign y = 1'b0;\n"
      "  child u(y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

// C2, input branch, non-ANSI port declaration: §23.2.2.3 resolves a port's
// direction from a separate `input` declaration in a non-ANSI header, a
// different production path from the ANSI headers above. Driving that input
// internally must warn just as the ANSI form does, exercising the non-ANSI
// direction-resolution path that produces the binding's direction end-to-end.
TEST(PortCoercionElaboration, NonAnsiInputPortDrivenWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(a);\n"
      "  input a;\n"
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

}  // namespace
