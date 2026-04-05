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

TEST(StreamingOperatorElaboration, StreamingTargetWiderThanStream) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] dst;\n"
      "  logic [7:0] a;\n"
      "  initial dst = {>> {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
