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

}  // namespace
