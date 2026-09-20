#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §8.3 (printed page 180) with §7.10 (printed 169), §7.5 and §7.4.2 (printed
// 154) and §26.2 (printed 808): a package queue, dynamic array and
// fixed-size array declared with a class's name hold handles, each element
// the 64 bits a module's handle has, so the queue's elements, the dynamic
// array's and each element variable of the fixed-size array are 64 bits
// wide. PackageDataWidth (lowerer_package_data.cpp) answered a handle's
// width for a scalar with no unpacked dimension alone and fell to 32 bits
// for the three, so an element held half an object id.
TEST(PackageImportSim, PackageHandleArrayElementsAreSixtyFourBitsWide) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  class C;\n"
      "    int v;\n"
      "  endclass\n"
      "  C q[$];\n"
      "  C d[];\n"
      "  C arr[2];\n"
      "endpackage\n"
      "module top;\n"
      "  import p1::*;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("p1.q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elem_width, 64u);
  auto* d = f.ctx.FindArrayInfo("p1.d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->elem_width, 64u);
  auto* elem = f.ctx.FindVariable("p1.arr[1]");
  ASSERT_NE(elem, nullptr);
  EXPECT_EQ(elem->value.width, 64u);
}

// §8.3 (printed page 180) with §7.10 (printed 169) and §26.3 (printed 808):
// the handles a module pushes into the package's queue of C are read back
// through the elements' property, `p1::q[0].v` the first object's 6 and
// `p1::q[1].v` the second's 8: 8 * 100 + 6. Read together with the width
// above so that an element held in a 64-bit slot still reaches its object as
// it did in the narrower one.
TEST(PackageImportSim, PackageQueueOfHandlesReadThroughElementProperties) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "    function new(int a); v = a; endfunction\n"
                      "  endclass\n"
                      "  C q[$];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    C c1 = new(6);\n"
                      "    C c2 = new(8);\n"
                      "    p1::q.push_back(c1);\n"
                      "    p1::q.push_back(c2);\n"
                      "    y = p1::q[1].v * 100 + p1::q[0].v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            806u);
}

// §8.25 (printed pages 203 and 204) with §8.7 (printed 184) and §26.2
// (printed 808): a package variable declared with a specialization and
// constructed by its own declaration assignment, `G #(5) b = new;`, holds an
// object of that specialization, whose N a method reads as 5, and a second
// variable `G #(7) c = new;` beside it an object of another specialization
// reading 7: 5 * 10 + 7. The initializer was evaluated as an ordinary
// expression, which constructs nothing, so `p1::b.get_n()` ran on no object
// and read the default 1 for both, 11; the object is now constructed once
// the package's classes are lowered (ConstructDataClassInitializers in
// lowerer_package_data.cpp) and bound to the declaration's actuals through
// the same ApplyClassParamOverrides a module's `G #(5) b = new` goes
// through, so 15 or 51 would say one specialization was bound to both.
TEST(PackageScopeReferenceSim,
     PackageClassVariableInitializerConstructsItsSpecialization) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class G #(int N = 1);\n"
                      "    function int get_n();\n"
                      "      return N;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  G #(5) b = new;\n"
                      "  G #(7) c = new;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int y;\n"
                      "  initial y = p1::b.get_n() * 10 + p1::c.get_n();\n"
                      "endmodule\n",
                      "y"),
            57u);
}

// §13.4 (printed page 340) with §26.3 (printed 808): a package void function
// named through the qualifier as a statement, `p1::set(5);`, runs as the
// call `p1::set(5)` in an expression does, and the value a nonvoid one
// discards under a void cast, `void'(p1::bump(1))`, is computed all the
// same, so the package's x reads 5 after the first and 6 after the second:
// 5 * 10 + 6. A statement that never ran its body would read 0 after the
// first, 50 or 0 in all, and a cast that skipped the call 55. Split off
// PackageFunctionWritesItsOwnQueueAndAssociativeArrayBare (26_03c) to pin
// the statement form apart from the objects that function writes.
TEST(PackageImportSim, PackageVoidFunctionCalledAsAStatementWritesItsPackage) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x;\n"
                      "  function void set(int v);\n"
                      "    x = v;\n"
                      "  endfunction\n"
                      "  function int bump(int v);\n"
                      "    x = x + v;\n"
                      "    return x;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int a, y;\n"
                      "  initial begin\n"
                      "    p1::set(5);\n"
                      "    a = p1::x;\n"
                      "    void'(p1::bump(1));\n"
                      "    y = a * 10 + p1::x;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            56u);
}

// §7.10 (printed page 169) with §26.2 (printed 808): the package's own
// queue, pushed by its own function's bare `q.push_back(v)` through the
// "p1.q" key ScopedObjectKeys puts first, holds the two values the two
// calls pushed, so size() reads 2 and q[1] the second: 2 * 10 + 6. The queue
// half of the 26_03c case alone, which reads 0 there because the
// associative-array half beside it answers x and the sum with it is x.
TEST(PackageImportSim, PackageFunctionWritesItsOwnQueueBare) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int q[$];\n"
                      "  function void add(int v);\n"
                      "    q.push_back(v);\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::add(5);\n"
                      "    p1::add(6);\n"
                      "    y = p1::q.size() * 10 + p1::q[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            26u);
}

// §7.8 (printed page 163) with §26.2 (printed 808): the package's own
// associative array, written by its function's bare `m["k"] = v` and read
// by another's bare `m["k"]`, both through the "p1.m" key, holds the 5 the
// first wrote: 5. The write side of the 26_03c case alone, read without the
// qualifier so that the entry's presence is pinned apart from the read
// through `p1::m[...]` below.
TEST(PackageImportSim, PackageFunctionWritesItsOwnAssociativeArrayReadBare) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int m[string];\n"
                      "  function void put(int v);\n"
                      "    m[\"k\"] = v;\n"
                      "  endfunction\n"
                      "  function int get();\n"
                      "    return m[\"k\"];\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::put(5);\n"
                      "    y = p1::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            5u);
}

// §7.8 (printed page 163) with §26.3 (printed 808): the entry the package's
// function wrote is read through the package scope resolution operator,
// `p1::m["k"]`, which names the same array under its "p1.m" key: 5. The
// select resolved no array -- ScopeResolvedAssocProperty
// (eval_array_class_assoc.cpp) took `p1::m` for a static property of a class
// named p1, unlike ScopeResolvedQueueProperty's `p1::q` -- so it fell to a
// bit-select of the 32-bit carrier at the string's value, out of range, and
// answered x, which the 2-state y stored as 0 with no diagnostic. An empty
// array with the entry missed would answer 0 as well, which the bare read
// above tells apart.
TEST(PackageImportSim,
     PackageFunctionWritesItsOwnAssociativeArrayReadThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int m[string];\n"
                      "  function void put(int v);\n"
                      "    m[\"k\"] = v;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::put(5);\n"
                      "    y = p1::m[\"k\"];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            5u);
}

// §7.8 (printed page 163) with §26.3 (printed 808): the mirror, an entry
// written through the qualifier, `p1::m["k"] = 7`, and read by the package's
// own function: 7. The write goes through the same resolver as the read
// above (TryAssocIndexedWrite through FindAssocArrayOfBase), so with `p1::m`
// resolving no array it landed on the carrier and the function read the
// missing entry's 0.
TEST(PackageImportSim,
     PackageAssociativeArrayWrittenThroughTheQualifierReadBare) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int m[string];\n"
                      "  function int get();\n"
                      "    return m[\"k\"];\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::m[\"k\"] = 7;\n"
                      "    y = p1::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            7u);
}

}  // namespace
