#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(CaseProductionRun, TheClausesSelectPicksByDeviceAndSevenWithADefault) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int device, i, devices[5];\n"
      "  initial begin\n"
      "    devices[0] = 8; devices[1] = 9; devices[2] = 10; devices[3] = 11; "
      "devices[4] = 16;\n"
      "    for (i = 0; i < 5; i++) begin\n"
      "      device = devices[i];\n"
      "      $write(\"%0d:\", device);\n"
      "      randsequence()\n"
      "        SELECT : case ( device & 7 )\n"
      "          0       : NETWORK ;\n"
      "          1, 2    : DISK ;\n"
      "          default : MEMORY ;\n"
      "        endcase ;\n"
      "        NETWORK : { $write(\"network \"); } ;\n"
      "        DISK    : { $write(\"disk \"); } ;\n"
      "        MEMORY  : { $write(\"memory \"); } ;\n"
      "      endsequence\n"
      "    end\n"
      "    $display(\"\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8:network 9:disk 10:disk 11:memory 16:network \n");
}

TEST(CaseProductionRun, TheFirstMatchWinsAndNoMatchWithoutDefaultIsNothing) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int first_wins = 0, nothing = 1;\n"
      "  initial begin\n"
      "    randsequence()\n"
      "      PICK : case ( 1 )\n"
      "        1 : A ;\n"
      "        1 : B ;\n"
      "      endcase ;\n"
      "      A : { first_wins = 1; } ;\n"
      "      B : { first_wins = 2; } ;\n"
      "    endsequence\n"
      "    randsequence()\n"
      "      PICK : case ( 5 )\n"
      "        1 : A ;\n"
      "        2 : A ;\n"
      "      endcase ;\n"
      "      A : { nothing = 0; } ;\n"
      "    endsequence\n"
      "    $display(\"%0d %0d\", first_wins, nothing);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

}  // namespace
