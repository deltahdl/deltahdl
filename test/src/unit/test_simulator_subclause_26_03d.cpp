#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.19.2 (printed page 121, Table 6-10) with §26.6 (printed 815): `VAL[3]`
// generates the constants VAL0, VAL1 and VAL2, valued 0, 1 and 2, and a
// wildcard export hands the constants p1 declares on under p2's qualifier,
// so `p2::VAL2` and `p2::VAL1` are p1's: 2 * 10 + 1. The export walk held the
// member under its written name VAL, which no storage answers, so nothing
// was bound under "p2.VAL2" and both read 0. The reads stand in a declaration
// initializer: the elaborator's provided-name walk (AddEnumMemberNames in
// elaborator_scope_rules_names.cpp) holds the member under its written name
// too, so the same reads in a procedural statement are reported there as
// names p2 neither declares nor exports, a check that reaches no initializer.
TEST(PackageImportSim, WildcardReExportedRangedLiteralThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef enum {VAL[3]} t;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y = p2::VAL2 * 10 + p2::VAL1;\n"
                      "endmodule\n",
                      "y"),
            21u);
}

// §6.19.2 (printed page 121) with §26.6 (printed 815): an export naming one
// generated constant, `export p1::VAL2`, hands that constant on, so `p2::VAL2`
// and `p2::VAL1` after two such exports are p1's 2 and 1: 2 * 10 + 1. The
// walk matched a named export against the written names of the members
// alone, VAL2 among none of them, so neither key was bound and both read 0.
TEST(PackageImportSim, ExplicitlyReExportedRangedLiteralThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef enum {VAL[3]} t;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::VAL2;\n"
                      "  export p1::VAL1;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p2::VAL2 * 10 + p2::VAL1;\n"
                      "endmodule\n",
                      "y"),
            21u);
}

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
