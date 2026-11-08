#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StdBuiltInPackageSim, StdQualifiedProcessSelfNamesTheRunningProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] non_null, same;\n"
      "  initial begin\n"
      "    automatic std::process p = std::process::self();\n"
      "    automatic process q = process::self();\n"
      "    non_null = (p != null) ? 1 : 0;\n"
      "    same = (p == q) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"non_null", 1u}, {"same", 1u}});
}

TEST(StdBuiltInPackageSim, StdQualifiedProcessHandleStatusAndStateLiterals) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] st, lits;\n"
      "  initial begin\n"
      "    automatic std::process p = std::process::self();\n"
      "    st = p.status();\n"
      "    lits = std::process::RUNNING + 10 * std::process::KILLED;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"st", 1u}, {"lits", 41u}});
}

TEST(StdBuiltInPackageSim, StdQualifiedProcessSelfHandleKillsTheChild) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    std::process p;\n"
      "    x = 7;\n"
      "    fork\n"
      "      begin\n"
      "        p = std::process::self();\n"
      "        #10 x = 99;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.kill();\n"
      "    #20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"x", 7u}});
}

TEST(StdBuiltInPackageSim, ModuleLevelStdProcessStateVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  std::process::state ms;\n"
                       "  initial begin\n"
                       "    std::process::state ls;\n"
                       "    ms = std::process::FINISHED; "
                       "ls = std::process::RUNNING;\n"
                       "    $display(\"%s %s\", ms.name(), ls.name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "FINISHED RUNNING\n");
}

TEST(StdPackageSim, ProceduralStdSemaphoreHoldsTheBuiltinObject) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int a, b;\n"
                       "  initial begin\n"
                       "    automatic std::semaphore s = new(1);\n"
                       "    a = s.try_get(1);\n"
                       "    b = s.try_get(1);\n"
                       "    $display(\"a=%0d b=%0d\", a, b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "a=1 b=0\n");
}

TEST(StdPackageSim, ProceduralStdMailboxHoldsTheBuiltinObject) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int n, ok, v;\n"
                       "  initial begin\n"
                       "    automatic std::mailbox m = new;\n"
                       "    m.put(23);\n"
                       "    n = m.num();\n"
                       "    ok = m.try_get(v);\n"
                       "    $display(\"n=%0d ok=%0d v=%0d\", n, ok, v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=1 ok=1 v=23\n");
}

TEST(StdPackageSim, StdSemaphoreBesideAUserClassIsTheBuiltin) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  class semaphore;\n"
                 "    int keys;\n"
                 "    function new(int k = 0); keys = k + 40; endfunction\n"
                 "  endclass\n"
                 "  std::semaphore s = new(1);\n"
                 "  semaphore u = new(2);\n"
                 "  int a, b;\n"
                 "  initial begin\n"
                 "    a = s.try_get(1);\n"
                 "    b = s.try_get(1);\n"
                 "    $display(\"a=%0d b=%0d u=%0d\", a, b, u.keys);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "a=1 b=0 u=42\n");
}

TEST(StdPackageSim, StdMailboxBesideAUserClassIsTheBuiltin) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  class mailbox;\n"
                       "    int n = 5;\n"
                       "  endclass\n"
                       "  std::mailbox m = new;\n"
                       "  int n, v;\n"
                       "  initial begin\n"
                       "    m.put(31);\n"
                       "    n = m.num();\n"
                       "    void'(m.try_get(v));\n"
                       "    $display(\"n=%0d v=%0d\", n, v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=1 v=31\n");
}

}  // namespace
