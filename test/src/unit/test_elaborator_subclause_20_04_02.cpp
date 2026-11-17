#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PrinttimescaleElab, DISABLED_AnArgumentBeyondTheSyntaxIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  timeunit 1ns / 1ns;\n"
      "  int x;\n"
      "  initial begin\n"
      "    $printtimescale();\n"
      "    $printtimescale(top, top);\n"
      "    $printtimescale(1 + 1);\n"
      "    $printtimescale(top.x + 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line = 5; line <= 8; ++line) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "$printtimescale takes no argument or one hierarchical identifier",
        line, "20.4.2"))
        << "line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

TEST(PrinttimescaleElab, TheFormsTheSyntaxGivesAreAccepted) {
  EXPECT_TRUE(
      ElabOk("timeunit 100ps / 10fs;\n"
             "module c;\n"
             "  timeunit 1us / 1ns;\n"
             "endmodule\n"
             "module top;\n"
             "  timeunit 1ns / 1ns;\n"
             "  c c1();\n"
             "  initial begin\n"
             "    $printtimescale;\n"
             "    $printtimescale(top);\n"
             "    $printtimescale(top.c1);\n"
             "    $printtimescale($unit);\n"
             "    $printtimescale($root);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(PrinttimescaleElab, DISABLED_ANameResolvingToNothingIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  initial $printtimescale(nosuch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'nosuch' resolves to no "
                            "declaration",
                            2, "23.8"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
