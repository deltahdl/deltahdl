#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(TimingCheckEventDefElaboration, TimingCheckEventNegedgeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(negedge clk, data, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckEventDefElaboration, TimingCheckEventPosedgeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckEventDefElaboration, TerminalPartSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data[3:0], posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckEventDefElaboration, TerminalBitSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data[0], posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

std::vector<uint32_t> ErrorLinesOf(const std::string& check) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [3:0] a, input clk, output q);\n"
      "  reg n;\n"
      "  wire [3:0] dc;\n"
      "  wire dd;\n"
      "  integer i;\n"
      "  specparam K = 1;\n"
      "  specify\n"
      "    " +
          check +
          ";\n"
          "  endspecify\n"
          "endmodule\n",
      f);
  std::vector<uint32_t> lines;
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.severity == DiagSeverity::kError) lines.push_back(d.loc.line);
  }
  return lines;
}

TEST(TimingCheckEventDefElaboration, AConstantTerminalSelectIsAccepted) {
  for (const char* check :
       {"$setup(a[K], posedge clk, 1)", "$hold(posedge clk, a[K:0], 1)",
        "$width(posedge a[K+:1], 1)",
        "$setuphold(posedge clk, a[K-:2], 1, 2, n, , , dc[K], dd)"}) {
    EXPECT_TRUE(ErrorLinesOf(check).empty()) << check;
  }
}

TEST(TimingCheckEventDefElaboration,
     DISABLED_ANonConstantTerminalSelectIsRejected) {
  for (const char* check :
       {"$setup(a[i], posedge clk, 1)", "$hold(posedge clk, a[i:0], 1)",
        "$width(posedge a[i+:1], 1)",
        "$setup(a[0+:i], posedge clk &&& a[i], 1)",
        "$setuphold(posedge clk, a[1], 1, 2, n, , , dc[i], dd)"}) {
    EXPECT_EQ(ErrorLinesOf(check), std::vector<uint32_t>{8}) << check;
  }
}

}  // namespace
