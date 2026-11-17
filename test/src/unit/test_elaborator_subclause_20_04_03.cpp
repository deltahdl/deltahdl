#include <gtest/gtest.h>

#include <cstdint>

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

TEST(TimeformatElab, AFifthArgumentAndAShortCallInAFunctionAreRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  function void k();\n"
      "    $timeformat(-9, 2);\n"
      "  endfunction\n"
      "  initial $timeformat(-9, 2, \" ns\", 10, 1);\n"
      "endmodule\n",
      f);
  const char* message = "'$timeformat' takes all four of its arguments or none";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 3, "20.4.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 5, "20.4.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(TimeformatElab, DISABLED_AShortCallInAClassOrPackageSubroutineIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  function void f();\n"
      "    $timeformat(-9, 2);\n"
      "  endfunction\n"
      "endclass\n"
      "package pk;\n"
      "  function void g();\n"
      "    $timeformat(-9, 2);\n"
      "  endfunction\n"
      "  task h();\n"
      "    $timeformat(-9, 2, \"x\");\n"
      "  endtask\n"
      "endpackage\n"
      "module t;\n"
      "endmodule\n",
      f);
  const char* message = "'$timeformat' takes all four of its arguments or none";
  for (uint32_t line : {3u, 8u, 11u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "20.4.3"))
        << "line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(TimeformatElab, FullCallsInAClassAndAPackageAreAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static function void f();\n"
             "    $timeformat(-9, 2, \"ns\", 8);\n"
             "  endfunction\n"
             "endclass\n"
             "package pk;\n"
             "  task h();\n"
             "    $timeformat;\n"
             "  endtask\n"
             "endpackage\n"
             "module t;\n"
             "endmodule\n"));
}

}  // namespace
