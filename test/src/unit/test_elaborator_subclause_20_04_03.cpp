#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// Syntax 20-5 (§20.4.3) gives $timeformat either no argument list or all four
// of units_number, precision_number, suffix_string and minimum_field_width, so
// a call with one, two or three of them is an error, in a process or in a
// subroutine.
TEST(TimeformatElab, ACallWithFewerThanFourArgumentsIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9);\n"
      "    $timeformat(-9, 2);\n"
      "  end\n"
      "  task k;\n"
      "    $timeformat(-9, 2, \" ns\");\n"
      "  endtask\n"
      "endmodule\n",
      f);
  const char* message = "'$timeformat' takes all four of its arguments or none";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 3, "20.4.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 4, "20.4.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 7, "20.4.3"));
}

// §20.4.3: the bare call and the call with all four arguments are the two forms
// Syntax 20-5 gives, and neither is reported.
TEST(TimeformatElab, ABareCallAndAFullCallAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat;\n"
      "    $timeformat(-9, 2, \" ns\", 10);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
