#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StreamExpressionConcatElaboration, NestedStreamingConcatAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [15:0] b;\n"
      "  initial b = {>> {{<< {a}}, a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamExpressionConcatElaboration, MultipleElementsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  logic [23:0] dst;\n"
      "  initial dst = {>> {a, b, c}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.14.1: a non-null class handle streams its data members in turn. It is
// illegal to stream a handle whose class exposes a local member, because that
// member is not accessible at the point of the streaming operator. This is a
// distinct application of the rule from the bit-stream cast of §6.24.3: a bare
// handle in a streaming concatenation never forms a cast node.
TEST(StreamExpressionConcatElaboration, ClassHandleWithLocalMemberRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class Hidden;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Hidden h;\n"
      "  int v;\n"
      "  initial v = {>> {h}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §11.4.14.1: a protected member is likewise inaccessible at the streaming
// operator, so the handle is illegal as a streaming concatenation operand.
TEST(StreamExpressionConcatElaboration,
     ClassHandleWithProtectedMemberRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class Hidden;\n"
      "  protected int guarded;\n"
      "endclass\n"
      "module m;\n"
      "  Hidden h;\n"
      "  int v;\n"
      "  initial v = {>> {h}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §11.4.14.1: an operand that is not a bit-stream type, an unpacked array, a
// struct, a union, or a class handle cannot be packed; the procedure's final
// branch issues an error. A real variable is such a non-streamable operand.
TEST(StreamExpressionConcatElaboration, RealOperandRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  logic [63:0] dst;\n"
      "  initial dst = {>> {r}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §11.4.14.1: a chandle is likewise not a bit-stream type, so it is an illegal
// streaming concatenation operand.
TEST(StreamExpressionConcatElaboration, ChandleOperandRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  chandle c;\n"
      "  logic [63:0] dst;\n"
      "  initial dst = {>> {c}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §11.4.14.1: an event is another type that is neither a bit-stream type nor a
// streamable aggregate, so the final branch rejects it as a streaming
// concatenation operand.
TEST(StreamExpressionConcatElaboration, EventOperandRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  logic [7:0] dst;\n"
      "  initial dst = {>> {e}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §11.4.14.1: a class handle whose members are all accessible (public) may be
// streamed; its data members are packed without error.
TEST(StreamExpressionConcatElaboration, ClassHandleWithPublicMembersAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Plain;\n"
      "  int a;\n"
      "  int b;\n"
      "endclass\n"
      "module m;\n"
      "  Plain p;\n"
      "  int v;\n"
      "  initial v = {>> {p}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
