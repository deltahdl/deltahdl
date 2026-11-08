#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "source of a streaming concatenation unpack must "
                            "be a bit-stream type or another streaming "
                            "concatenation",
                            4, "11.4.14.3"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "source of a streaming concatenation unpack must "
                            "be a bit-stream type or another streaming "
                            "concatenation",
                            4, "11.4.14.3"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "source of a streaming concatenation unpack must "
                            "be a bit-stream type or another streaming "
                            "concatenation",
                            4, "11.4.14.3"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "source of a streaming concatenation unpack must "
                            "be a bit-stream type or another streaming "
                            "concatenation",
                            4, "11.4.14.3"));
}

TEST(StreamingUnpackElaboration, NetInContinuousStreamingTargetRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [3:0] w, n;\n"
      "  logic [3:0] v, u, t, x;\n"
      "  assign {>>{w}} = x;\n"
      "  assign {>>{v, {<<{n}}}} = {x, x};\n"
      "  assign {>>{u}} = x;\n"
      "  assign {<<{{t, w}}} = {x, x};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a streaming concatenation written as a target "
                            "unpacks into variables, and 'w' is a net",
                            4, "11.4.14.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a streaming concatenation written as a target "
                            "unpacks into variables, and 'n' is a net",
                            5, "11.4.14.3"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "'v' is a net", 5, "11.4.14.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "unpacks into variables", 6,
                             "11.4.14.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a streaming concatenation written as a target "
                            "unpacks into variables, and 'w' is a net",
                            7, "11.4.14.3"));
}

}  // namespace
