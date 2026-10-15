#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §26.7 (Syntax 26-5): a name of the built-in package may be written behind
// `std::`, so `std::process::self()` is §9.7's `process::self()` and answers
// the handle of the calling process rather than null. The two handles name
// one process, so they compare equal.
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

// §9.7 through §26.7: the handle `std::process::self()` answers is the calling
// process, so its status() is RUNNING (1) and not the zero state a null handle
// reports; the enum literals reached as `std::process::RUNNING` and
// `std::process::KILLED` are §9.7's 1 and 4.
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

// §9.7 through §26.7: a child's `std::process::self()` handle is the child, so
// the parent's kill() through it stops the child before its delayed write; a
// null handle would kill nothing and the write would land.
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

// A.2.2.1 with §26.7: a module-level variable declared `std::process::state`
// is of the enumeration §9.7 declares, so it holds a member and name()
// answers it, as a procedural one does.
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

// §26.7 (printed page 817): `std::semaphore` names the built-in class, so a
// procedural variable declared so holds the semaphore new builds: its one key
// is given up once and then gone. The scoped name was recognised as no
// built-in class and no semaphore was bound, so both calls answered 0.
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

// The same for `std::mailbox`: the message put is counted and taken back.
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

// §26.7 with §15.2: a class the module declares named semaphore is what the
// bare name means there, but `std::semaphore` still reaches the built-in
// class, whose one key is given up once. The handle was recorded as the
// module's class, which has no try_get, and both calls answered 0.
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

// The same for `std::mailbox` beside a class the module names mailbox.
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
