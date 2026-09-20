#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

namespace {

// A package p declaring `typedef mailbox mb_t` and the subroutine
// `subroutine`, whose formal is written `mb_t m` bare, with a module that
// imports nothing of p, puts one message into its own mailbox and reaches the
// subroutine through `call`, the package scope resolution operator naming it
// (§26.3, printed page 808).
std::string PackageTypedefFormalSrc(const std::string& subroutine,
                                    const std::string& call) {
  return "package p;\n"
         "  typedef mailbox mb_t;\n" +
         subroutine +
         "endpackage\n"
         "module top;\n"
         "  mailbox mb = new;\n"
         "  int y;\n"
         "  initial begin\n"
         "    mb.put(1);\n" +
         call +
         "  end\n"
         "endmodule\n";
}

// §26.2 (printed page 808) makes a package's declarations visible by their
// bare names throughout the package -- the clause's own ComplexPkg declares
// `add(Complex a, b)` with the package's typedef written bare -- and §6.18
// (printed 118) makes the typedef name stand for the type it renames, so
// `mb_t m` is a `mailbox m` formal, which §13.5.1 (printed 348) with §8.2
// copies in as the handle to the caller's mailbox: count(mb) reads the one
// message as 1. The run keys the package's typedef "p::mb_t" and a module's
// `import p::*` is what adds the bare key, so with no import the bare name
// the formal wrote found nothing, the formal was a plain 32-bit value, num()
// found no mailbox on any path and y read 0.
TEST(PassByValueSim, PackageFunctionMailboxFormalThroughThePackagesOwnTypedef) {
  EXPECT_EQ(RunAndGet(PackageTypedefFormalSrc(
                          "  function automatic int count(mb_t m);\n"
                          "    return m.num();\n"
                          "  endfunction\n",
                          "    y = p::count(mb);\n"),
                      "y"),
            1u);
}

// The same binding for a package task's formal, which §13.3 (printed page
// 335) enables as a statement and whose actuals are bound as a function's
// are: `p::count_into(mb, y)` writes its output formal from the mailbox
// formal's num(), 1 for the one message, where the plain-value formal left
// y at 0.
TEST(PassByValueSim, PackageTaskMailboxFormalThroughThePackagesOwnTypedef) {
  EXPECT_EQ(RunAndGet(PackageTypedefFormalSrc(
                          "  task automatic count_into(mb_t m, output int n);\n"
                          "    n = m.num();\n"
                          "  endtask\n",
                          "    p::count_into(mb, y);\n"),
                      "y"),
            1u);
}

}  // namespace
