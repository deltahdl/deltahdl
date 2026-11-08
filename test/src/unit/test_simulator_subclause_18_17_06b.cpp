#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(AbortingProductionsRun, TheClausesReturnAbortsP2OnceAndBTwice) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int flag;\n"
      "  initial begin\n"
      "    for (flag = 0; flag < 3; flag++) begin\n"
      "      $write(\"%0d:\", flag);\n"
      "      randsequence()\n"
      "        TOP : P1 P2 ;\n"
      "        P1  : A B C ;\n"
      "        P2  : A { if ( flag == 1 ) return; } B C ;\n"
      "        A   : { $write( \" A\" ); } ;\n"
      "        B   : { if ( flag == 2 ) return; $write( \" B\" ); } ;\n"
      "        C   : { $write( \" C\" ); } ;\n"
      "      endsequence\n"
      "      $display(\"\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0: A B C A B C\n1: A B C A\n2: A C A C\n");
}

TEST(AbortingProductionsRun, ABreakLeavesTheBlockUnlessALoopEnclosesIt) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int fifo_length = 4, max_length = 4, command = 0, data = 0, next = "
      "0;\n"
      "  int i, loop_ended = 0, went_on = 0, ungenerated, loop_only;\n"
      "  initial begin\n"
      "    randsequence()\n"
      "      WRITE   : SETUP DATA ;\n"
      "      SETUP   : { if ( fifo_length >= max_length ) break; } COMMAND ;\n"
      "      COMMAND : { command = 1; } ;\n"
      "      DATA    : { data = 1; } ;\n"
      "    endsequence\n"
      "    next = 1;\n"
      "    randsequence()\n"
      "      LOOP  : { for (i = 0; i < 10; i++) begin if (i == 3) break; end "
      "loop_ended = i == 3; } AFTER ;\n"
      "      AFTER : { went_on = 1; } ;\n"
      "    endsequence\n"
      "    ungenerated = command == 0 && data == 0;\n"
      "    loop_only = loop_ended && went_on;\n"
      "    $display(\"%0d %0d %0d\", ungenerated, next, loop_only);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1\n");
}

}  // namespace
