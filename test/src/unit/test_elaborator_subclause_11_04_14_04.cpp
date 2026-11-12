#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

TEST(StreamWithElaboration,
     DISABLED_AWithClauseOnAnythingButAOneDimensionalUnpackedArrayIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int x; endclass\n"
      "module m;\n"
      "  typedef struct { int f; } s_t;\n"
      "  logic [7:0] v; int i; s_t s; C h; int mm [2][3]; logic a [8];\n"
      "  logic [15:0] o; int q [$]; int d []; real r = 1.0;\n"
      "  wire [15:0] w = {>> {v with [3:0]}};\n"
      "  initial begin\n"
      "    o = {>> {v with [3:0]}};\n"
      "    o = {>> {i with [0:1]}};\n"
      "    o = {>> {s with [0:1]}};\n"
      "    o = {>> {h with [0:1]}};\n"
      "    o = {>> {mm with [0:1]}};\n"
      "    o = {>> {{<< {a}} with [0:1]}};\n"
      "    {>> {v with [3:0]}} = o;\n"
      "    {>> {i with [0:1]}} <= o;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (const int kLine : {6, 8, 9, 10, 11, 12, 13, 14, 15}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a with clause applies only to a "
                              "one-dimensional unpacked array",
                              kLine, "11.4.14.4"))
        << kLine;
  }
}

TEST(StreamWithElaboration,
     AWithClauseOnOneDimensionalUnpackedArraysIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int x; endclass\n"
      "module m;\n"
      "  typedef struct { int f; } s_t;\n"
      "  logic [7:0] v; int i; s_t s; C h; int mm [2][3]; logic a [8];\n"
      "  logic [15:0] o; int q [$]; int d []; real r = 1.0;\n"
      "  wire [15:0] w = 16'({>> {a with [0:1]}});\n"
      "  initial begin\n"
      "    o = 16'({>> {a with [0:1]}});\n"
      "    o = 16'({>> {mm[0] with [0:1]}});\n"
      "    {>> {q with [0:2]}} = 96'h0;\n"
      "    {>> {d with [0:1]}} <= 64'h0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StreamWithElaboration,
     DISABLED_ANonIntegralWithRangeExpressionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int x; endclass\n"
      "module m;\n"
      "  typedef struct { int f; } s_t;\n"
      "  logic [7:0] v; int i; s_t s; C h; int mm [2][3]; logic a [8];\n"
      "  logic [15:0] o; int q [$]; int d []; real r = 1.0;\n"
      "  initial begin\n"
      "    o = 16'({>> {a with [1.5]}});\n"
      "    o = 16'({>> {a with [0 : r]}});\n"
      "    o = 16'({>> {a with [r +: 2]}});\n"
      "    o = 16'({>> {a with [3 -: r]}});\n"
      "    o = 16'({>> {a with [\"s\"]}});\n"
      "    o = 16'({>> {a with [h]}});\n"
      "    o = 16'({>> {a with [0 : s]}});\n"
      "    {>> {q with [0 : r]}} = o;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (const int kLine : {7, 8, 9, 10, 11, 12, 13, 14}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a with range expression shall be of integral "
                              "type",
                              kLine, "11.4.14.4"))
        << kLine;
  }
}

TEST(StreamWithElaboration, IntegralWithRangeExpressionsAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int x; endclass\n"
      "module m;\n"
      "  typedef struct { int f; } s_t;\n"
      "  logic [7:0] v; int i; s_t s; C h; int mm [2][3]; logic a [8];\n"
      "  logic [15:0] o; int q [$]; int d []; real r = 1.0;\n"
      "  initial begin\n"
      "    o = 16'({>> {a with [1]}});\n"
      "    o = 16'({>> {a with [0 : i]}});\n"
      "    o = 16'({>> {a with [i +: 2]}});\n"
      "    o = 16'({>> {a with [3 -: 2]}});\n"
      "    {>> {q with [0 : i]}} = o;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StreamWithElaboration, DISABLED_AConstantWithRangeOutOfBoundsIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int x; endclass\n"
      "module m;\n"
      "  typedef struct { int f; } s_t;\n"
      "  logic [7:0] v; int i; s_t s; C h; int mm [2][3]; logic a [8];\n"
      "  logic [15:0] o; int q [$]; int d []; real r = 1.0;\n"
      "  initial begin\n"
      "    {>> {q with [-1 : 2]}} = o;\n"
      "    {>> {d with [-2 +: 2]}} = o;\n"
      "    {>> {a with [6 : 9]}} = o;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a with range on a dynamic array or queue shall be "
                            "non-negative",
                            7, "11.4.14.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a with range on a dynamic array or queue shall be "
                            "non-negative",
                            8, "11.4.14.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "streaming unpack with-range exceeds fixed array "
                            "bounds",
                            9, "11.4.14.4"));
}

}  // namespace
