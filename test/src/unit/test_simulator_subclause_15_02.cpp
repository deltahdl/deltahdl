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

}  // namespace
