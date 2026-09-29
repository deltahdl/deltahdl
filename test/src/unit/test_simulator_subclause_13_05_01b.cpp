#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
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
                      "    static C first = new;\n"
                      "    result = init(null) * 100 + init();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            909u);
}

// §13.5 with §10.8 and §10.9.1: an assignment pattern written as the actual of
// an unpacked-array input formal is assigned to the formal, so each element
// takes the value the pattern gives its position -- positional, replicated by
// default or keyed, on an ascending or a descending formal -- evaluated in the
// caller. Bound as a value, the pattern's concatenated bits reached the formal
// as one vector, and f('{1, 2, 3}) read 110.
TEST(PassByValueSim, AssignmentPatternActualFillsAnArrayFormal) {
  EXPECT_EQ(
      RunAndGet(
          "module t;\n"
          "  function automatic int f(int a[3]); "
          "return a[0] * 100 + a[1] * 10 + a[2]; endfunction\n"
          "  function automatic int g(int a[2:0]); "
          "return a[2] * 100 + a[1] * 10 + a[0]; endfunction\n"
          "  int x = 5;\n"
          "  int r;\n"
          "  initial r = f('{1, 2, 3}) + 1000 * f('{default: 2}) +\n"
          "             1000000 * g('{1, 2, 3}) - f('{0: x, default: 1});\n"
          "endmodule\n",
          "r"),
      123u + 222000u + 123000000u - 511u);
}

// §13.5 with §6.18 and §7.4.4: a formal declared through a typedef of an
// unpacked array has the typedef's dimensions, so an assignment pattern bound
// to it fills its elements, typed or untyped, and an output formal of it
// hands its elements back. Taken for one element, the pattern's bits reached
// the formal as one vector, f('{1, 2, 3}) reading 110, and the output
// formal's elements went nowhere.
TEST(PassByValueSim, FormalOfAnArrayTypedefHasItsDimensions) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef int arr_t[3];\n"
                 "  function automatic int f(arr_t a); "
                 "return a[0] * 100 + a[1] * 10 + a[2]; endfunction\n"
                 "  task automatic o(output arr_t r); r = '{4, 5, 6}; endtask\n"
                 "  arr_t ov;\n"
                 "  initial begin\n"
                 "    o(ov);\n"
                 "    $display(\"%0d %0d %0d %p\", f('{1, 2, 3}), "
                 "f(arr_t'{1, 2, 3}), f('{default: 2}), ov);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "123 123 222 '{4, 5, 6}\n");
}

// §13.5.1 with §7.2.1: a fixed-size array formal passed by value holds copies
// of the caller's elements, each of the formal's element type, so `b[1].lo`
// selects a member of a packed structure element in a function and in a task
// alike. The element variables were bound to no layout, and the member read 0.
TEST(PassByValueSim, MemberOfAnElementOfAPackedStructureArrayFormal) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } B;\n"
                "module t;\n"
                "  function automatic int f(input B b[2]);\n"
                "    return b[1].lo * 10 + b[0].hi;\n"
                "  endfunction\n"
                "  task automatic tk(input B b[2], output int r);\n"
                "    r = b[1].hi;\n"
                "  endtask\n"
                "  B arr[2];\n"
                "  int r;\n"
                "  initial begin\n"
                "    arr[0] = '{hi: 3, lo: 1}; arr[1] = '{hi: 9, lo: 2};\n"
                "    tk(arr, r);\n"
                "    $display(\"%0d %0d\", f(arr), r);\n"
                "  end\n"
                "endmodule\n",
                f),
            "23 9\n");
}

// §13.3 has an output formal copy its value out when the subroutine returns,
// and §6.21 with §6.8 (Table 6-7) starts each variable of an automatic
// subroutine's call at its type's default: x for `logic` and for the
// elements of a `logic` array, 0 for `int` and `bit`. An output the body never
// writes therefore copies out that default. Every output formal started at 0,
// and the 4-state ones copied out 0 where they hold x.
TEST(PassByValueSim, UnwrittenOutputFormalCopiesOutItsTypesDefault) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module t;\n"
                "  function automatic void f(output logic [3:0] l,\n"
                "                            output int i,\n"
                "                            output bit [3:0] b);\n"
                "  endfunction\n"
                "  task automatic tk(output logic [1:0] a[2]); endtask\n"
                "  logic [3:0] l = 4'b1010; int i = 7; bit [3:0] b = 4'b1111;\n"
                "  logic [1:0] a[2] = '{2'b01, 2'b10};\n"
                "  initial begin\n"
                "    f(l, i, b); tk(a);\n"
                "    $display(\"%b %0d %b %b %b\", l, i, b, a[0], a[1]);\n"
                "  end\n"
                "endmodule\n",
                f),
            "xxxx 0 0000 xx xx\n");
}

}  // namespace
