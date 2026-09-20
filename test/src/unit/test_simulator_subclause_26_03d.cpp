#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §26.3 (printed page 810) with §8.7 (printed 184): `import p1::h` makes
// p1's class-handle variable locally visible under its bare name, and `h =
// new` constructs an object of the class it is declared with into p1's h, so
// the property written through the bare name reads back through it and
// through p1's qualifier alike: 5 * 10 + 5. The import bound the bare name
// to the storage alone, with no class recorded under it, so the `new` had no
// class to construct, the handle stayed null and both reads answered 0.
TEST(PackageImportSim, ImportedClassHandleConstructedThroughTheBareName) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::h;\n"
                      "  import p1::C;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    h.v = 5;\n"
                      "    y = h.v * 10 + p1::h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            55u);
}

// §26.3 (printed page 810) with §8.7: a wildcard import makes p1's h
// potentially locally visible, the reference binding it, and `h = new`
// constructs p1's C into it as the explicit import's does: 5 * 10 + 5 read
// through the bare name and p1's qualifier. The wildcard path binds the bare
// name through the same alias, which carried no class record, so the handle
// stayed null and both reads answered 0.
TEST(PackageImportSim,
     WildcardImportedClassHandleConstructedThroughTheBareName) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    h.v = 5;\n"
                      "    y = h.v * 10 + p1::h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            55u);
}

}  // namespace
