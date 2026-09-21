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

// §13.5.1 with §8.2 (printed page 180): a formal declared with a class type
// is passed the object handle, so it is as wide as one and the body may
// assign it an object whatever the actual was. uvm_init's `cs =
// dcs` under `uvm_coreservice_t cs = null` is this. init(null) and init()
// both construct a D and store it in cs, whose get() reads D's 9, packed as
// 909. The formal took the width of the actual it arrived with, and the
// literal null is a bit wide, so the handle was cut to its low bit: 0, the
// null that answered 1, or 1, the handle of the C the module constructed
// first, whose get() answered 5.
TEST(PassByValueSim, ClassFormalBoundFromNullHoldsTheObjectTheBodyAssigns) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int k = 5;\n"
                      "  function int get(); return k; endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  function new(); k = 9; endfunction\n"
                      "endclass\n"
                      "function automatic int init(C cs = null);\n"
                      "  D d;\n"
                      "  if (cs == null) begin\n"
                      "    d = new;\n"
                      "    cs = d;\n"
                      "  end\n"
                      "  return cs == null ? 1 : cs.get();\n"
                      "endfunction\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C first = new;\n"
                      "    result = init(null) * 100 + init();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            909u);
}

}  // namespace
