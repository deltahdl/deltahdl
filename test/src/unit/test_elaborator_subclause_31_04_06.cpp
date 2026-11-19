#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TimingCheckEventDefElaboration, NochangeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, 0, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckEventDefElaboration, NochangeNegativeOffsetsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, -5, -5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckEventDefElaboration, NochangeSpecparamOffsetsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam so = 5, eo = 7;\n"
      "    $nochange(posedge clk, data, so, eo);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckEventDefElaboration, NochangeDeclaredNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg nt;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, 0, 0, nt);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

void ExpectNochangeOffsetRejected(const char* offsets, const char* name) {
  ElabFixture f;
  std::string src =
      "module m(input clk, data);\n"
      "  wire [7:0] w;\n"
      "  logic [7:0] v;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, ";
  src += offsets;
  src +=
      ");\n"
      "  endspecify\n"
      "endmodule\n";
  ElaborateSrc(src, f);
  std::string msg = "timing check limit operand '";
  msg += name;
  msg += "' is not a specparam";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 5, "31.2")) << src;
}

TEST(TimingCheckEventDefElaboration, NochangeNetOrVariableOffsetRejected) {
  ExpectNochangeOffsetRejected("w, 0", "w");
  ExpectNochangeOffsetRejected("v, 0", "v");
  ExpectNochangeOffsetRejected("0, w", "w");
  ExpectNochangeOffsetRejected("0, v", "v");
}

}  // namespace
