#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

// §15.2: semaphore and mailbox are classes of the std package (§26.7), so a
// class the module declares under the name is the one a module variable and
// a procedural variable of that type hold, built by its own constructor and
// read through its own properties: s.keys is 2 + 40 and t.keys 5 + 40. Built
// as the built-in semaphore, neither held an object of the user's class.
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

// §15.2: a class of the compilation unit named mailbox is the type of both the
// unit's variable and the module's, and their put() is the class's own: mb
// reads 7 + 30 and umb 7 + 5.
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

// §15.2: a package's class named semaphore is the type of the package's own
// variable, constructed by the class's new: p::s.keys reads 3 + 40.
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

// §15.2 with §7.4: an element of an array of the user's semaphore class is
// given an object of that class by new: arr[1].keys reads 4 + 40.
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
