#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StreamingOperatorElaboration, StreamingAsAssignmentSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial dst = {>> {a, b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingOperatorElaboration, StreamingWithBitStreamCast) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial b = int'({<< byte {a}});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingOperatorElaboration, StreamingNestedInStreaming) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [15:0] b;\n"
      "  initial b = {>> {{<< {a}}}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingOperatorElaboration, RealTargetForStreamingSourceRejected) {
  // §11.4.14: a streaming_concatenation source requires a bit-stream-type
  // target; a real variable is not a bit-stream type and shall be rejected.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  real dst;\n"
      "  logic [7:0] a;\n"
      "  initial dst = {>> {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(StreamingOperatorElaboration, EventTargetForStreamingSourceRejected) {
  // §11.4.14: event variables are likewise not bit-stream types.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  logic [7:0] a;\n"
      "  initial e = {>> {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(StreamingOperatorElaboration, StreamingAsArithOperandRejected) {
  // §11.4.14: a streaming_concatenation appearing as a sub-operand of an
  // expression (here, the right operand of `+`) without a prior bit-stream
  // cast is illegal.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial dst = a + {>> {b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
