#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §15.4 (printed page 374) and §15.4.1 (printed 374) with §26.2 (printed
// 808): a package's `mailbox mb = new` is an unbounded queue before any
// procedure starts, so `p1::mb.put(7)` and `p1::mb.put(9)` place two
// messages, `p1::mb.get(a)` retrieves the first in the order they were
// placed (§15.4.5) and num() counts the one left (§15.4.2): 7 * 10 + 1. The
// package's storage was a plain Variable, the initializer evaluated into it
// and no MailboxObject made under "p1.mb", so the two put() statements and
// the get() were served by no mailbox, a stayed 0 and num() answered
// nothing: 0. A queue that placed both messages and retrieved none would
// read 2.
TEST(PackageImportSim, PackageMailboxInitializedByNewThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  mailbox mb = new;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int a, y;\n"
                      "  initial begin\n"
                      "    p1::mb.put(7);\n"
                      "    p1::mb.put(9);\n"
                      "    p1::mb.get(a);\n"
                      "    y = a * 10 + p1::mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            71u);
}

// §15.4.1 (printed page 374) with §26.2 (printed 808) and §11.2.1: a nonzero
// bound is the size of the queue, and a package's new(D) reads D, the
// package's own parameter, by its bare name in the package's frame, so the
// first try_put() places its message and the second finds the queue full
// (§15.4.4): 1 * 10 + 0. A bound that never reached the queue, or a D read
// as 0, would leave it unbounded and both try_put() calls placing: 11; no
// mailbox under "p1.mb" at all served neither call: 0.
TEST(PackageImportSim, PackageMailboxBoundReadsThePackagesOwnParameter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  localparam int D = 1;\n"
                      "  mailbox mb = new(D);\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    y = p1::mb.try_put(3) * 10 + p1::mb.try_put(4);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

// §26.2 (printed page 808) lets a package's items reference what the package
// itself declares, and §13.3 and §13.4 run a subroutine's body in the scope
// declaring it, so the bare `mb` inside p1::send and p1::offer is p1's
// mailbox, the one `p1::mb` reaches through §26.3's scope resolution
// operator: send(4) places a message through put() (§15.4.3), offer(5)
// places another through try_put() and answers 1 (§15.4.4), and num() then
// counts two (§15.4.2): 1 * 10 + 2. Under the defect no mailbox stood under
// "p1.mb", the key FindMailbox tries through the package frame, so the put()
// ran on nothing, try_put() answered 0 and num() nothing: 0. A mailbox the
// task reached and the function missed would read 1, the other way round 11.
TEST(PackageImportSim, PackageSubroutinesReachTheirOwnMailboxBare) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  mailbox mb = new;\n"
                      "  task send(int v);\n"
                      "    mb.put(v);\n"
                      "  endtask\n"
                      "  function int offer(int v);\n"
                      "    return mb.try_put(v);\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::send(4);\n"
                      "    y = p1::offer(5) * 10 + p1::mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            12u);
}

// §15.4.1 (printed page 374) with §26.2 (printed 808): a package's `mailbox
// mb` with no initializer is an unbounded queue, as a module's is
// (CreateMailboxForVar in lowerer_var.cpp), and a procedural `p1::mb =
// new(1)` then builds it with a bound of one (TryMailboxNewAssign), so the
// first try_put() places its message and the second finds the queue full:
// 1 * 10 + 0. Under the same defect no queue stood under "p1.mb", so the
// new() found no mailbox to build and both try_put() calls were served by
// none: 0. A queue created but not rebuilt by the new() would read 11.
TEST(PackageImportSim,
     PackageMailboxDeclaredWithoutInitializerBuiltThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  mailbox mb;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::mb = new(1);\n"
                      "    y = p1::mb.try_put(3) * 10 + p1::mb.try_put(4);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

// §15.3.1 (printed page 373) with §26.2 (printed 808) and §11.2.1: a
// package's `semaphore s = new(K)` reads K, the package's own parameter, by
// its bare name in the package's frame once K holds its value, so the bucket
// starts with two keys and two try_get(1) calls procure one each: 1 * 10 +
// 1. The key count was read when the bucket was created, ahead of the
// parameters' own initializers (InitPackageDataItem), when "p1.K" held the
// 0 its storage was created with, so the bucket started empty and both calls
// procured none: 0. A count read as 1 would read 10.
TEST(PackageImportSim, PackageSemaphoreKeyCountReadsThePackagesOwnParameter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  localparam int K = 2;\n"
                      "  semaphore s = new(K);\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    y = p1::s.try_get(1) * 10 + p1::s.try_get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            11u);
}

}  // namespace
