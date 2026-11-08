#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StreamReorderingElaboration, LeftShiftElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = {<< {b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamReorderingElaboration, RightShiftElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = {>> {b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamReorderingElaboration, TypeSliceSizeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = {<< byte {b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamReorderingElaboration, IntegerSliceSizeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial b = {<< 8 {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamReorderingElaboration, ZeroSliceSizeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {<< 0 {a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "streaming slice_size shall be a positive constant",
                            3, "11.4.14.2"));
}

TEST(StreamReorderingElaboration, NegativeSliceSizeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {<< (-1) {a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "streaming slice_size shall be a positive constant",
                            3, "11.4.14.2"));
}

TEST(StreamReorderingElaboration, ComputedZeroSliceSizeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {<< (2 - 2) {a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "streaming slice_size shall be a positive constant",
                            3, "11.4.14.2"));
}

TEST(StreamReorderingElaboration, ComputedPositiveSliceSizeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {<< (4 - 1) {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamReorderingElaboration, ParameterZeroSliceSizeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter W = 0;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {<< (W + 0) {a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "streaming slice_size shall be a positive constant",
                            4, "11.4.14.2"));
}

TEST(StreamReorderingElaboration, LocalparamPositiveSliceSizeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam W = 8;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {<< (W + 0) {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamReorderingElaboration, ZeroSliceSizeNames11_4_14_2) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {<< 0 {a}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "streaming slice_size shall be a positive constant",
                            3, "11.4.14.2"));
}

TEST(StreamSliceSizeElaboration, ParameterSliceSizeOfZeroReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  parameter Z = 0, W = 8;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  logic [15:0] r;\n"
      "  initial r = {<< Z {16'hABCD}};\n"
      "  initial r = {<< W {16'hABCD}};\n"
      "  initial r = {<< nib_t {16'hABCD}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "streaming slice_size shall be a positive constant",
                            5, "11.4.14.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(StreamSliceSizeElaboration, SizedAndBasedLiteralSliceSizesFoldedByValue) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic [15:0] r;\n"
      "  initial r = {<< 4'd0 {16'hABCD}};\n"
      "  initial r = {<< 'h0 {16'hABCD}};\n"
      "  initial r = {<< 'h8 {16'hABCD}};\n"
      "  initial r = {<< 4'b1000 {16'hABCD}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "streaming slice_size shall be a positive constant",
                            3, "11.4.14.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "streaming slice_size shall be a positive constant",
                            4, "11.4.14.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace
