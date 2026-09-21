#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/variable.h"

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

// §26.3 (printed page 810) with §27.3 (printed 818): an import written in a
// generate block makes the package's names visible in the block, and the
// block's process names the package's own `int a[2]` and `int q[$]` by their
// bare names, so `a[1] = 7` writes the element p1's get(1) reads and the two
// pushes fill the queue p1's qs() sizes: 7 * 10 + 2. The alias keyed the
// array's shape, its elements and the queue under the block's import prefix
// (AliasImportedPackageName in lowerer_import.cpp), which the process's
// FindArrayInfo and FindQueue tried no key of: the write set bit 1 of the
// carrier, so get(1) read 0, and the pushes reached no queue, so qs() read 0.
TEST(PackageImportSim,
     GenerateBlockImportedArrayElementAndQueueReadByThePackage) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[2];\n"
                      "  int q[$];\n"
                      "  function int get(int i);\n"
                      "    return a[i];\n"
                      "  endfunction\n"
                      "  function int qs();\n"
                      "    return q.size();\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  if (1) begin : blk\n"
                      "    import p1::*;\n"
                      "    initial begin\n"
                      "      a[1] = 7;\n"
                      "      q.push_back(2);\n"
                      "      q.push_back(3);\n"
                      "    end\n"
                      "  end\n"
                      "  initial #1 y = p1::get(1) * 10 + p1::qs();\n"
                      "endmodule\n",
                      "y"),
            72u);
}

// §12.7.3 with §26.3 (printed page 810) and §27.3 (printed 818): foreach
// over the name a generate block's import brings in reads the package
// array's shape, three elements, so the loop runs three times. With the
// shape found under no key of the block the loop ran once per bit of the
// 32-bit carrier: 32.
TEST(PackageImportSim, GenerateBlockImportedArrayCountedByForeach) {
  EXPECT_EQ(RunAndGet("package p2;\n"
                      "  int a[3];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int n = 0;\n"
                      "  if (1) begin : g\n"
                      "    import p2::*;\n"
                      "    initial foreach (a[i]) n++;\n"
                      "  end\n"
                      "endmodule\n",
                      "n"),
            3u);
}

// §20.7 with §26.3 (printed page 810) and §27.3 (printed 818): $size of each
// name a generate block's import brings in is that package array's element
// count, 2 and 4: 2 * 10 + 4. With the shapes found under no key of the
// block each query saw a 32-bit scalar and answered its width: 352.
TEST(PackageImportSim, GenerateBlockImportedArraySizeQueried) {
  EXPECT_EQ(RunAndGet("package p3;\n"
                      "  int a[2];\n"
                      "  int b[4];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  if (1) begin : blk\n"
                      "    import p3::*;\n"
                      "    initial y = $size(a) * 10 + $size(b);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            24u);
}

// §7.4.2 (printed page 154) with §26.3 (printed 810) and §27.3 (printed
// 818): the block's own process writes two elements of the imported array
// and reads them back through the same import: 7 * 10 + 3. With the shape
// found under no key of the block each write set one bit of the carrier,
// bit 1 to 7's low bit and bit 0 to 3's, and each read answered that bit:
// 1 * 10 + 1.
TEST(PackageImportSim, GenerateBlockImportedArrayElementReadInTheBlock) {
  EXPECT_EQ(RunAndGet("package p4;\n"
                      "  int a[2];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y2;\n"
                      "  if (1) begin : blk\n"
                      "    import p4::*;\n"
                      "    initial begin\n"
                      "      a[1] = 7;\n"
                      "      a[0] = 3;\n"
                      "      y2 = a[1] * 10 + a[0];\n"
                      "    end\n"
                      "  end\n"
                      "endmodule\n",
                      "y2"),
            73u);
}

// A design whose package p5 declares the packed structure st2, a 4-bit a
// above a 12-bit b, and `st2 u = '{b: 12'hBCD, a: 4'hA};`, and a module top
// whose items are `top_items`; answers the top's y.
static uint64_t PackageStructRead(const std::string& top_items) {
  return RunAndGet(
      "package p5;\n"
      "  typedef struct packed { logic [3:0] a; logic [11:0] b; } st2;\n"
      "  st2 u = '{b: 12'hBCD, a: 4'hA};\n"
      "endpackage\n"
      "module top;\n" +
          top_items + "endmodule\n",
      "y");
}

// §26.3 (printed page 810) with §7.2.1 (printed 147) and §10.9.2 (printed
// 263): `p5::u.b` names the member b of the package's own `st2 u`, laid out
// as st2 lays it, so the keyed pattern's 12'hBCD is read back from b. The
// package's storage stood under "p5.u" with no layout registered for it
// (CreatePackageDataVariables in lowerer_package_data.cpp), so the read
// resolved through no member and answered 0, and the pattern was
// concatenated in written order rather than placed by member.
TEST(PackageImportSim, PackageStructVariableMemberReadThroughItsScopedName) {
  EXPECT_EQ(PackageStructRead("  int y;\n"
                              "  initial y = p5::u.b;\n"),
            0xBCDu);
}

// §26.3 (printed page 810) with §7.2.1 (printed 147): a wildcard import
// makes the package's u visible under its bare name, the one variable the
// package declares, so `u.b` reads the same 12'hBCD `p5::u.b` does. The
// import bound the carrier variable alone, with none of its layout
// (AliasVariableKinds), so the read resolved through no member and answered
// 0.
TEST(PackageImportSim, ImportedPackageStructVariableMemberReadByItsBareName) {
  EXPECT_EQ(PackageStructRead("  import p5::*;\n"
                              "  int y;\n"
                              "  initial y = u.b;\n"),
            0xBCDu);
}

// §26.3 (printed page 810) with §11.9 (printed 304): the imported bare u
// and `p6::u` name the one package variable, which has one tag, so after the
// module's `u = tagged Other 3;` the read `p6::u.Valid` is inconsistent with
// Other and is reported at its line, naming the union by the scoped spelling
// the read used. The retag was recorded under the module's bare name
// (TagKeyOfName in eval_member_path.cpp) while the read asked under "p6.u"
// and found the initializer's Valid there, so the 3 was read as Valid
// unreported; the refused read's x becomes 0 in the 2-state y (§6.11.2),
// which reads apart from that 3.
TEST(PackageImportSim,
     ImportedPackageTaggedUnionRetaggedByItsBareNameIsOneTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p6;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u = tagged Valid 9;\n"
      "endpackage\n"
      "module top;\n"
      "  import p6::*;\n"
      "  int y;\n"
      "  initial begin\n"
      "    u = tagged Other 3;\n"
      "    y = p6::u.Valid;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  Variable* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "run-time error: accessing member 'Valid' of tagged union 'p6.u' "
      "which currently has tag 'Other'",
      10, "11.9"));
}

// §26.3 with §6.8 (Table 6-7, printed page 107): a package variable with no
// declaration assignment holds its type's default -- 'x for a logic, 0 for
// an int, "" for a string, 0.0 for a real -- and the one storage is read
// through the package scope, `P::pl`, and through the bare name a wildcard
// import binds, `pl`, alike. A package's `logic pl` read 0 both ways.
TEST(PackageImportSim, UninitializedPackageVariablesHoldTheirTypesDefaults) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "package P;\n"
          "  logic pl; int pn; string ps; real pr;\n"
          "endpackage\n"
          "module t;\n"
          "  import P::*;\n"
          "  initial begin\n"
          "    $display(\"pl=%0h pn=%0d ps=[%s] pr=%f\", pl, pn, ps, pr);\n"
          "    $display(\"ql=%0h qn=%0d qs=[%s] qr=%f\", P::pl, P::pn,\n"
          "             P::ps, P::pr);\n"
          "  end\n"
          "endmodule\n",
          f),
      "pl=x pn=0 ps=[] pr=0.000000\nql=x qn=0 qs=[] qr=0.000000\n");
}

}  // namespace
