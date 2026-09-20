#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §26.3 (printed page 810) with §7.4.2 (printed 154) and §13.4: a wildcard
// import makes the package's `int a[2]` visible under its bare name, and the
// name denotes the package's own array, so `a[1] = 7` in the module writes
// the element the package's function reads by its bare `a[1]`: 7 * 10 + 7.
// The import bound the carrier variable alone, with no ArrayInfo and no
// element aliases under the module's key (AliasVariableKinds in
// lowerer_import.cpp), so the write set bit 1 of the 32-bit carrier, the
// module's read answered that bit and the package's element held 0: 10.
TEST(PackageImportSim, ImportedPackageFixedSizeArrayElementWrittenAndRead) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[2];\n"
                      "  function int get(int i);\n"
                      "    return a[i];\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    a[1] = 7;\n"
                      "    y = a[1] * 10 + get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            77u);
}

// §12.7.3 with §7.4.2 (printed page 154) and §26.3 (printed 810): foreach
// over the imported name reads the package array's shape, two elements, so
// the loop runs twice. With no ArrayInfo under the import's key the loop
// ran once per bit of the 32-bit carrier: 32.
TEST(PackageImportSim, ImportedPackageFixedSizeArrayCountedByForeach) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[2];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int n = 0;\n"
                      "  initial foreach (a[i]) n++;\n"
                      "endmodule\n",
                      "n"),
            2u);
}

// §20.7 with §7.4.2 (printed page 154) and §26.3 (printed 810): $size of the
// imported name is the package array's element count, 2. With no ArrayInfo
// under the import's key the query saw a 32-bit scalar and answered its
// width: 32.
TEST(PackageImportSim, ImportedPackageFixedSizeArraySizeQueried) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[2];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial y = $size(a);\n"
                      "endmodule\n",
                      "y"),
            2u);
}

// §7.5 and §7.5.1 (printed pages 157-158) with §26.3 (printed 810): the
// package's function sizes its `int d[]` to three elements and writes the
// last, and the imported name is that dynamic array, so size() through it
// reads 3 and d[2] reads 4: 3 * 10 + 4. The import bound the carrier alone,
// with no QueueObject and no dynamic ArrayInfo under the module's key, so
// both reads answered 0.
TEST(PackageImportSim, ImportedPackageDynamicArraySizedByPackageFunction) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int d[];\n"
                      "  function void make();\n"
                      "    p1::d = new[3];\n"
                      "    p1::d[2] = 4;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    make();\n"
                      "    y = d.size() * 10 + d[2];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            34u);
}

// §26.6 (printed pages 815-816) with §26.3 (printed 810) and §7.4.2 (printed
// 154): p2's `export p1::*` hands p1's array on, so a module importing p2
// reads p1's `a[1]` under the bare name, the element p1's set() wrote, 5,
// and `p2::a` names the same array through the exporter's qualifier, so a
// foreach over it runs twice: 5 * 10 + 2. The import's alias carried no
// elements, so `a[1]` read bit 1 of the carrier, 0, and the exporter's key
// "p2.a" held no ArrayInfo, so the loop ran once per bit of the carrier:
// 0 * 10 + 32.
TEST(PackageImportSim, ExportedPackageFixedSizeArrayReadThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[2];\n"
                      "  function void set(int i, int v);\n"
                      "    a[i] = v;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p2::*;\n"
                      "  int n = 0;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::set(1, 5);\n"
                      "    foreach (p2::a[i]) n++;\n"
                      "    y = a[1] * 10 + n;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            52u);
}

}  // namespace
