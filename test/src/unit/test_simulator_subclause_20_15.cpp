#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(QueueCallPlacement, TheCallsRunInAnAutomaticTask) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  task automatic run(output integer s1, s2, s3, j, i, v);\n"
          "    $q_initialize(1, 1, 4, s1);\n"
          "    $q_add(1, 9, 5, s2);\n"
          "    $q_exam(1, 1, v, s3);\n"
          "    $q_remove(1, j, i, s3);\n"
          "  endtask\n"
          "  integer s1, s2, s3, j, i, v;\n"
          "  initial begin\n"
          "    run(s1, s2, s3, j, i, v);\n"
          "    $display(\"%0d %0d %0d %0d %0d %0d\", s1, s2, s3, j, i, v);\n"
          "  end\n"
          "endmodule\n",
          f),
      "0 0 0 9 5 1\n");
}

TEST(QueueCallPlacement, QFullRunsInAnAutomaticFunction) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  function automatic int full(int id, output integer s);\n"
                 "    return $q_full(id, s);\n"
                 "  endfunction\n"
                 "  integer st, s;\n"
                 "  int r;\n"
                 "  initial begin\n"
                 "    $q_initialize(1, 1, 1, st);\n"
                 "    $q_add(1, 1, 0, st);\n"
                 "    r = full(1, s);\n"
                 "    $display(\"%0d %0d\", r, s);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1 0\n");
}

TEST(QueueCallPlacement, DISABLED_TheCallsRunInAClassMethod) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    integer st, j, i;\n"
                       "    task run();\n"
                       "      $q_initialize(2, 2, 4, st);\n"
                       "      $q_add(2, 3, 30, st);\n"
                       "      $q_add(2, 4, 40, st);\n"
                       "      $q_remove(2, j, i, st);\n"
                       "    endtask\n"
                       "  endclass\n"
                       "  C h = new;\n"
                       "  initial begin\n"
                       "    h.run();\n"
                       "    $display(\"%0d %0d %0d\", h.st, h.j, h.i);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 4 40\n");
}

TEST(QueueCallPlacement, TheCallsRunInAProgramInitialBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p;\n"
                       "  integer st, j, i;\n"
                       "  initial begin\n"
                       "    $q_initialize(1, 1, 4, st);\n"
                       "    $q_add(1, 6, 60, st);\n"
                       "    $q_remove(1, j, i, st);\n"
                       "    $display(\"%0d %0d %0d\", st, j, i);\n"
                       "  end\n"
                       "endprogram\n"
                       "module t;\n"
                       "  p u();\n"
                       "endmodule\n",
                       f),
            "0 6 60\n");
}

TEST(QueueCallPlacement, TheCallsRunInAPackageTask) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  task automatic run(output integer st, j, i);\n"
                       "    $q_initialize(1, 1, 4, st);\n"
                       "    $q_add(1, 8, 80, st);\n"
                       "    $q_remove(1, j, i, st);\n"
                       "  endtask\n"
                       "endpackage\n"
                       "module t;\n"
                       "  import pk::*;\n"
                       "  integer st, j, i;\n"
                       "  initial begin\n"
                       "    run(st, j, i);\n"
                       "    $display(\"%0d %0d %0d\", st, j, i);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 8 80\n");
}

}  // namespace
