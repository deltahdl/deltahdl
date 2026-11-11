#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kSliceEndsTheSelect =
    "a part-select ends a select; no bracket follows it";

TEST(ArraySliceParsing, SliceInMoreThanOneDimensionIsReported) {
  auto r = Parse(
      "module top;\n"
      "  int a [4][4];\n"
      "  int b [2][2];\n"
      "  initial begin\n"
      "    b = a[0:1][1:2];\n"
      "    b = a[0 +: 2][1 +: 2];\n"
      "    b = a[0:1][1 +: 2];\n"
      "    a[0:1][1:2] = b;\n"
      "    b = a[0:1][0];\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line : {5, 6, 7, 8, 9}) {
    EXPECT_TRUE(ReportedError(r.diags, kSliceEndsTheSelect, line, "A.8.4"))
        << line;
  }
}

TEST(ArraySliceParsing, SliceInOneDimensionWithIndicesOnTheOthersIsAccepted) {
  auto r = Parse(
      "module top;\n"
      "  int a [4][4];\n"
      "  int b [2][2];\n"
      "  int c [2];\n"
      "  initial begin\n"
      "    c = a[1][1:2];\n"
      "    b[0] = a[1][1 -: 2];\n"
      "    b = a[2:3];\n"
      "    a[3][0 +: 2] = c;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
