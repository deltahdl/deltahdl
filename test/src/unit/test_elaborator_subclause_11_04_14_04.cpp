#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StreamingDynamicDataElaboration, WithClauseInPackContextAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr[4];\n"
      "  logic [31:0] dst;\n"
      "  initial dst = {>> byte {arr with [0 +: 2]}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingDynamicDataElaboration, WithClauseInUnpackContextAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr[4];\n"
      "  logic [31:0] src;\n"
      "  initial {>> byte {arr with [0 +: 2]}} = src;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingDynamicDataElaboration, WithFixedRangeAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr[8];\n"
      "  logic [31:0] dst;\n"
      "  initial dst = {<< byte {arr with [3:0]}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingDynamicDataElaboration, WithMinusRangeAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr[8];\n"
      "  logic [31:0] dst;\n"
      "  initial dst = {>> byte {arr with [7 -: 4]}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingDynamicDataElaboration, WithAmongMultipleElementsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] hdr, crc;\n"
      "  logic [7:0] payload[8];\n"
      "  int len;\n"
      "  logic [31:0] dst;\n"
      "  initial dst = {<< byte {hdr, payload with [0 +: 4], crc}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingDynamicDataElaboration, WithSimpleIndexAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr[4];\n"
      "  int dst;\n"
      "  initial dst = {>> int {arr with [2]}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StreamingDynamicDataElaboration, WithOnQueueAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte q[$];\n"
      "  logic [31:0] src;\n"
      "  initial {<< byte {q with [0 +: 4]}} = src;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
