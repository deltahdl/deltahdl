#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StreamingUnpackElaboration, StreamingConcatAsLhsRightShiftElab) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial {>> {a, b}} = 16'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingUnpackElaboration, StreamingConcatAsLhsLeftShiftElab) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial {<< byte {a, b}} = 16'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingUnpackElaboration, StreamingConcatAsLhsWithSliceSizeElab) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] v;\n"
      "  initial {<< 4 {v}} = 16'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingUnpackElaboration, StreamingConcatAsLhsFromStreamingRhsElab) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial {>> {a, b}} = {>> {c, d}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.14.3: the source of an unpack (the RHS driving a
// streaming_concatenation target) shall be of bit-stream type. A plain
// bit-stream variable source is the accepting case; it pairs with the two
// negatives below, which differ only in the source's declared type, so the flip
// in acceptance isolates the source-type rule enforced by
// CheckStreamingUnpackSourceType.
TEST(StreamingUnpackElaboration, UnpackFromBitStreamVarSourceAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  logic [15:0] s;\n"
      "  initial {>> {a, b}} = s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.14.3: a real source is not a bit-stream type, so unpacking from it into
// a streaming_concatenation target shall be rejected.
TEST(StreamingUnpackElaboration, UnpackFromRealSourceRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  real r;\n"
      "  initial {>> {a, b}} = r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §11.4.14.3: a chandle is likewise not a bit-stream type — a distinct
// non-bit-stream source from the real case above — so it is also rejected as an
// unpack source.
TEST(StreamingUnpackElaboration, UnpackFromChandleSourceRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  chandle c;\n"
      "  initial {>> {a, b}} = c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §11.4.14.3: an event is not a bit-stream type either — a third distinct
// non-bit-stream source type alongside real and chandle — so it is rejected as
// an unpack source.
TEST(StreamingUnpackElaboration, UnpackFromEventSourceRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  event e;\n"
      "  initial {>> {a, b}} = e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(StreamingUnpackElaboration, NonblockingAssignWithStreamingTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial {>> {a}} <= 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.14.3: the unpack source-type rule applies in the nonblocking-assignment
// position as well (a distinct statement kind in the streaming-context walk),
// not only the blocking form. A real source is rejected there too; this pairs
// with the accepting nonblocking case above, which differs only in source type.
TEST(StreamingUnpackElaboration, NonblockingUnpackFromRealSourceRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  real r;\n"
      "  initial {>> {a, b}} <= r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
