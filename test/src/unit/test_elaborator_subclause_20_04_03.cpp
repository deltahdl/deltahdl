#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(TimeformatElab, ACallWithAnEmptyArgumentListIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$timeformat' takes all four of its arguments or none", 3, "20.4.3"));
}

TEST(TimeformatElab, ACallLeavingAnArgumentPositionEmptyIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, , , 10);\n"
      "    $timeformat(-9, 2, \" ns\", );\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* message = "'$timeformat' takes all four of its arguments or none";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 3, "20.4.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 4, "20.4.3"));
}

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
