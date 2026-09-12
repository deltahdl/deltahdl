// Annex A.7.5 "System timing checks" holds no production of its own beyond
// those A.7.5.1, A.7.5.2 and A.7.5.3 track. What A.7.5.2 gives the two flags
// of $timeskew and $fullskew, `event_based_flag ::= constant_expression` and
// `remain_active_flag ::= constant_mintypmax_expression`, Table 31-8 and
// Table 31-9 state again for each: "Constant expression". These cases observe
// the elaborator holding a flag to that.

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// A flag that is a literal, a parameter, a localparam, a specparam of the
// block or a specparam of the module body is a constant expression.
TEST(TimingCheckFlagElaboration, ConstantFlagsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter EB = 1) (input clk1, clk2);\n"
      "  localparam RA = 0;\n"
      "  specparam sp_ra = 1;\n"
      "  specify\n"
      "    specparam sp_eb = 0;\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, , EB, RA);\n"
      "    $fullskew(posedge clk1, posedge clk2, 5, 6, , sp_eb, sp_ra);\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, , EB + 1, 0:1:2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A variable is no constant expression: $timeskew's event_based_flag naming
// one is reported at the check under §31.4.2, whose Table 31-8 describes the
// flag.
TEST(TimingCheckFlagElaboration, TimeskewVariableEventBasedFlagIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input clk1, clk2);\n"
      "  reg en;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, , en);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$timeskew event_based_flag is not a constant expression", 4, "31.4.2"));
}

// A net is no constant expression either: $timeskew's remain_active_flag
// naming one is reported, the event_based_flag before it being a literal.
TEST(TimingCheckFlagElaboration, TimeskewNetRemainActiveFlagIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input clk1, clk2);\n"
      "  wire act;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, , 1, act);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$timeskew remain_active_flag is not a constant expression",
                    4, "31.4.2"));
}

// $fullskew's flags are held the same way, under §31.4.3, whose Table 31-9
// describes them; a variable inside a larger expression is found there too,
// as is one inside a min:typ:max triple.
TEST(TimingCheckFlagElaboration, FullskewVariableFlagsAreRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input clk1, clk2);\n"
      "  reg en, act;\n"
      "  specify\n"
      "    $fullskew(posedge clk1, posedge clk2, 5, 6, , en | 1, act:1:2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$fullskew event_based_flag is not a constant expression", 4, "31.4.3"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$fullskew remain_active_flag is not a constant expression",
                    4, "31.4.3"));
}

}  // namespace
