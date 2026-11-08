#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(AlwaysProcedureInCheckers, GeneralAlwaysInCheckerIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk);\n"
      "  logic a;\n"
      "  always @(posedge clk) a <= 1'b1;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a general 'always' procedure cannot be used "
                            "inside checker 'chk'",
                            3, "17.5"));
}

TEST(AlwaysProcedureInCheckers, AlwaysFfInCheckerIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk);\n"
      "  logic a;\n"
      "  always_ff @(posedge clk) a <= 1'b1;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysProcedureInCheckers, AlwaysCombInCheckerIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  logic a, b;\n"
      "  always_comb a = b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysProcedureInCheckers, AlwaysLatchInCheckerIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic en);\n"
      "  logic a, b;\n"
      "  always_latch if (en) a = b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysProcedureInCheckers, GeneralAlwaysInCheckerGenerateIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk);\n"
      "  logic a, b, c, d;\n"
      "  if (1) begin : g1\n"
      "    always @(posedge clk) a <= 1'b1;\n"
      "  end else begin : g2\n"
      "    always @(posedge clk) b <= 1'b1;\n"
      "  end\n"
      "  for (genvar i = 0; i < 1; i++) begin : g3\n"
      "    always @(posedge clk) c <= 1'b1;\n"
      "  end\n"
      "  case (1)\n"
      "    default: begin : g4\n"
      "      always @(posedge clk) d <= 1'b1;\n"
      "    end\n"
      "  endcase\n"
      "endchecker\n",
      f, "chk");
  for (uint32_t line : {4u, 6u, 9u, 13u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a general 'always' procedure cannot be used "
                              "inside checker 'chk'",
                              line, "17.5"))
        << line;
  }
}

TEST(AlwaysProcedureInCheckers, AlwaysFfInCheckerGenerateIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk);\n"
      "  logic a;\n"
      "  if (1) begin : g\n"
      "    always_ff @(posedge clk) a <= 1'b1;\n"
      "  end\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysProcedureInCheckers, GeneralAlwaysOutsideCheckerIsStillAllowed) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic clk);\n"
      "  logic a;\n"
      "  always @(posedge clk) a <= 1'b1;\n"
      "endmodule\n",
      f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysProcedureInCheckers,
     GeneralAlwaysRejectedAlongsideAcceptedSpecializedForms) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk);\n"
      "  logic a, b, c;\n"
      "  always_comb c = b;\n"
      "  always @(posedge clk) a <= b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a general 'always' procedure cannot be used "
                            "inside checker 'chk'",
                            4, "17.5"));
}

}  // namespace
