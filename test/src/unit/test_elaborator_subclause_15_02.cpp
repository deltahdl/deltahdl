#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §15.2: semaphore and mailbox are classes of the std package (§26.7), so user
// code may declare a class of either name, and a handle of it is checked
// against the user's class rather than the std class's prototype (§G.3, §G.4).
// The semaphore prototype's constructor takes at most one argument.
TEST(BuiltinClassRedefinitionElab,
     ModuleClassNamedSemaphoreTakesItsConstructor) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class semaphore;\n"
      "    function new(int a, int b, int c); endfunction\n"
      "  endclass\n"
      "  semaphore s = new(1, 2, 3);\n"
      "  initial begin\n"
      "    semaphore t = new(4, 5, 6);\n"
      "    t = new(7, 8, 9);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.2: a class of the compilation unit's scope named mailbox is the one the
// module's handle is of, whose methods the mailbox prototype does not declare.
TEST(BuiltinClassRedefinitionElab, UnitClassNamedMailboxTakesItsMethods) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class mailbox;\n"
      "  function void send(int a, int b); endfunction\n"
      "  function void put(int a, int b); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  mailbox mb = new;\n"
      "  initial begin\n"
      "    mb.send(1, 2);\n"
      "    mb.put(3, 4);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.2: a module that declares no class of the name still reaches the std
// package's semaphore, whose prototype the call is checked against.
TEST(BuiltinClassRedefinitionElab, OtherModulesSemaphoreIsTheBuiltIn) {
  ElabFixture f;
  ElaborateSrc(
      "module a;\n"
      "  class semaphore;\n"
      "    function void grab(int n); endfunction\n"
      "  endclass\n"
      "endmodule\n"
      "module m;\n"
      "  semaphore s = new(1);\n"
      "  a ua();\n"
      "  initial s.grab(1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'semaphore' declares no method 'grab'", 9,
                            "G.3"));
}

}  // namespace
