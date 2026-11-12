#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(BuiltinClassRedefinitionSim, ModuleClassNamedSemaphoreIsTheUsersClass) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class semaphore;\n"
      "    int keys;\n"
      "    function new(int k = 0); keys = k + 40; endfunction\n"
      "  endclass\n"
      "  semaphore s = new(2);\n"
      "  int r;\n"
      "  initial begin\n"
      "    automatic semaphore t = new(5);\n"
      "    r = s.keys * 100 + t.keys;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4245u);
}

TEST(BuiltinClassRedefinitionSim, UnitClassNamedMailboxIsTheUsersClass) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class mailbox;\n"
      "  int tag;\n"
      "  function new(); tag = 7; endfunction\n"
      "  function void put(int v); tag = tag + v; endfunction\n"
      "endclass\n"
      "mailbox umb = new;\n"
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int r;\n"
      "  initial begin\n"
      "    mb.put(30);\n"
      "    umb.put(5);\n"
      "    r = mb.tag * 100 + umb.tag;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3712u);
}

TEST(BuiltinClassRedefinitionSim, PackageClassNamedSemaphoreIsTheUsersClass) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "package p;\n"
      "  class semaphore;\n"
      "    int keys;\n"
      "    function new(int k = 0); keys = k + 40; endfunction\n"
      "  endclass\n"
      "  semaphore s = new(3);\n"
      "endpackage\n"
      "module t;\n"
      "  int r;\n"
      "  initial r = p::s.keys;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 43u);
}

TEST(BuiltinClassRedefinitionSim, ArrayOfAClassNamedSemaphoreHoldsItsObjects) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class semaphore;\n"
      "    int keys;\n"
      "    function new(int k = 0); keys = k + 40; endfunction\n"
      "  endclass\n"
      "  semaphore arr[2];\n"
      "  int r;\n"
      "  initial begin\n"
      "    arr[1] = new(4);\n"
      "    r = arr[1].keys;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

TEST(BuiltInSyncClassSim,
     StdQualifiedNamesReachTheBuiltInsBesideARedefinition) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module m;\n"
          "  class semaphore;\n"
          "    int keys;\n"
          "    function new(int k = 0); keys = k + 100; endfunction\n"
          "  endclass\n"
          "  class Logged extends std::mailbox #(int);\n"
          "    int puts;\n"
          "    task send(int v);\n"
          "      puts++;\n"
          "      put(v);\n"
          "    endtask\n"
          "  endclass\n"
          "  semaphore mine = new(1);\n"
          "  std::semaphore real_sem = new(1);\n"
          "  Logged lm = new;\n"
          "  initial begin\n"
          "    int v, got;\n"
          "    got = real_sem.try_get(1);\n"
          "    $display(\"mine=%0d got=%0d again=%0d\", mine.keys, got, "
          "real_sem.try_get(1));\n"
          "    lm.send(7);\n"
          "    lm.send(8);\n"
          "    lm.get(v);\n"
          "    $display(\"puts=%0d v=%0d n=%0d\", lm.puts, v, lm.num());\n"
          "  end\n"
          "endmodule\n",
          f),
      "mine=101 got=1 again=0\nputs=2 v=7 n=1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(BuiltInSyncClassSim, DISABLED_ADerivedClassesMethodHidesTheBuiltInOne) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module m;\n"
          "  class Counted extends semaphore;\n"
          "    int puts, gets, tries;\n"
          "    function new(int k = 0); super.new(k); endfunction\n"
          "    function void put(int n = 1); puts++; super.put(n); "
          "endfunction\n"
          "    task get(int n = 1); gets++; super.get(n); endtask\n"
          "    function int try_get(int n = 1); tries++; return "
          "super.try_get(n); endfunction\n"
          "  endclass\n"
          "  class Mb extends mailbox;\n"
          "    int gets, peeks, tries, nums;\n"
          "    task get(ref int v); gets++; super.get(v); endtask\n"
          "    task peek(ref int v); peeks++; super.peek(v); endtask\n"
          "    function int try_put(int v); tries++; return super.try_put(v); "
          "endfunction\n"
          "    function int num(); nums++; return super.num(); endfunction\n"
          "  endclass\n"
          "  Counted s = new(1);\n"
          "  Mb b = new;\n"
          "  initial begin\n"
          "    int v, n;\n"
          "    s.get(1);\n"
          "    s.put(1);\n"
          "    void'(s.try_get(1));\n"
          "    void'(b.try_put(4));\n"
          "    b.peek(v);\n"
          "    b.get(v);\n"
          "    n = b.num();\n"
          "    $display(\"%0d %0d %0d | %0d %0d %0d %0d\", s.gets, s.puts, "
          "s.tries, b.tries, b.peeks, b.gets, b.nums);\n"
          "    begin\n"
          "      semaphore h;\n"
          "      mailbox g;\n"
          "      h = s;\n"
          "      g = b;\n"
          "      h.put(1);\n"
          "      n = g.num();\n"
          "      $display(\"%0d %0d\", s.puts, b.nums);\n"
          "    end\n"
          "  end\n"
          "endmodule\n",
          f),
      "1 1 1 | 1 1 1 1\n1 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
