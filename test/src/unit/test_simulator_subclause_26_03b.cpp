#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackageScopeReferenceSim, PackageScopedStructVariableHasItsMembers) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  typedef struct packed {\n"
                      "    logic [7:0] id;\n"
                      "    logic [15:0] val;\n"
                      "  } rec_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  pk::rec_t r;\n"
                      "  logic [31:0] result;\n"
                      "  initial begin\n"
                      "    r.id = 7;\n"
                      "    r.val = 300;\n"
                      "    result = r * 16;\n"
                      "    r = 24'h07012c;\n"
                      "    result = result + r.id;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0x07012c * 16u + 7u);
}

TEST(PackageScopeReferenceSim, PackageFunctionCalledThroughItsScopedName) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  function automatic int mix(int n);\n"
                      "    return n * n + 1;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module t;\n"
                      "  logic [31:0] y;\n"
                      "  initial y = pk::mix(6) * 100 + pk::mix(3);\n"
                      "endmodule\n",
                      "y"),
            3710u);
}

TEST(PackageScopeReferenceSim,
     PackageFunctionCalledThroughItsScopedNameInAClassMethod) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  function automatic int mix(int n);\n"
                      "    return n * n + 1;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "class U;\n"
                      "  function int via(int k);\n"
                      "    return pk::mix(k) + 1000;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  logic [31:0] y;\n"
                      "  initial begin\n"
                      "    static U u = new;\n"
                      "    y = u.via(4);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1017u);
}

TEST(PackageScopeReferenceSim,
     PackageVoidFunctionEnabledThroughItsScopedNameWritesItsOutput) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  function automatic void pf(input int n = 1,\n"
                      "                             output int r);\n"
                      "    r = n * 3;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int a, b;\n"
                      "  logic [31:0] y;\n"
                      "  initial begin\n"
                      "    pk::pf(.r(a), .n(9));\n"
                      "    pk::pf(4, b);\n"
                      "    y = a * 100 + b;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            2712u);
}

TEST(PackageImportSim, CuScopeWildcardImportedClassAsBaseHandleType) {
  auto val = RunAndGet(
      "package pk;\n"
      "  class B; int b = 3;\n"
      "    virtual function int who(); return 1; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "import pk::*;\n"
      "class D extends B;\n"
      "  virtual function int who(); return 2; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r;\n"
      "  B h; D d = new;\n"
      "  initial begin\n"
      "    h = d;\n"
      "    r = h.who() * 10 + d.b;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 23u);
}

TEST(PackageScopeReferenceSim,
     PackageFunctionReadsAndWritesItsPackageVariable) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  int base = 30;\n"
                      "  function automatic int get(); return base;\n"
                      "  endfunction\n"
                      "  function automatic void set(int v); base = v;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    out = pk::get() * 100;\n"
                      "    pk::set(31);\n"
                      "    out = out + pk::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            30u * 100u + 31u);
}

TEST(PackageScopeReferenceSim, PackageFunctionReadsAVariableItsPackageImports) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  int base = 30;\n"
                      "endpackage\n"
                      "package pq;\n"
                      "  import pk::*;\n"
                      "  function automatic int get(); return base;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial out = pq::get();\n"
                      "endmodule\n",
                      "out"),
            30u);
}

TEST(PackageScopeReferenceSim, PackageFunctionDefaultReadsThePackageScope) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  int base = 30;\n"
                      "  function automatic int get(int v = base); return v;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int base = 1;\n"
                      "  int out;\n"
                      "  initial out = pk::get() * 10 + pk::get(base);\n"
                      "endmodule\n",
                      "out"),
            30u * 10u + 1u);
}

TEST(PackageScopeReferenceSim, PackageEnumConstantReadThroughItsScope) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  parameter int BASE = 5;\n"
                      "  typedef enum {LOW, MED = 2, HIGH} sev_t;\n"
                      "  typedef enum {A = BASE + 1, B} step_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial out = pk::HIGH * 100 + pk::B;\n"
                      "endmodule\n",
                      "out"),
            307u);
}

TEST(PackageScopeReferenceSim, CompoundAssignmentToAScopedPackageVariable) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int shared = 100;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    p::shared += 150;\n"
                      "    p::shared++;\n"
                      "    out = p::shared;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            251u);
}

TEST(PackageScopeReferenceSim,
     CompoundAssignmentToAScopedPackageVariableInAMethod) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int shared = 100;\n"
                      "endpackage\n"
                      "class Writer;\n"
                      "  function void bump(int n); p::shared += n;\n"
                      "  endfunction\n"
                      "  function void inc(); p::shared++; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static Writer w = new;\n"
                      "    w.bump(150);\n"
                      "    out = p::shared * 1000;\n"
                      "    w.inc();\n"
                      "    out = out + p::shared;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            250u * 1000u + 251u);
}

TEST(PackageScopeReferenceSim, PackageVariableWithoutInitializerIsWritable) {
  EXPECT_EQ(RunAndGet("package P;\n"
                      "  int pn;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import P::*;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    P::pn = 17;\n"
                      "    out = P::pn * 100 + pn;\n"
                      "    pn = 23;\n"
                      "    out = out * 100 + P::pn;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            (17u * 100u + 17u) * 100u + 23u);
}

TEST(PackageScopeReferenceSim, PackageVariableWithoutInitializerKeepsItsType) {
  EXPECT_EQ(RunAndGet("package P;\n"
                      "  logic pl; int pn; string ps;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    P::ps = \"name2\";\n"
                      "    out = P::ps.len() * 100 + $isunknown(P::pl) * 10 +\n"
                      "          (P::pn == 0 ? 0 : 1);\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            510u);
}

TEST(PackageScopeReferenceSim,
     PackageVariableInitializedFromAPackageFunctionCall) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int sq(int a); return a * a; endfunction\n"
                      "  int v = sq(8);\n"
                      "  int u = v + 1;\n"
                      "endpackage\n"
                      "package q;\n"
                      "  import p::*;\n"
                      "  int w = sq(8);\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial out = p::v * 10000 + q::w * 100 + p::u;\n"
                      "endmodule\n",
                      "out"),
            64u * 10000u + 64u * 100u + 65u);
}

TEST(PackageImportSim, ExplicitImportOfAnEnumLiteralReadsItsValue) {
  EXPECT_EQ(RunAndGet("package q;\n"
                      "  typedef enum { ORIGINAL, FALSE } teeth_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import q::teeth_t, q::FALSE;\n"
                      "  teeth_t a;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    a = FALSE;\n"
                      "    out = a * 10 + FALSE;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            11u);
}

TEST(PackageImportSim, ExplicitImportOfAnEnumLiteralShadowsAWildcardsLiteral) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef enum { FALSE, TRUE } bool_t;\n"
                      "endpackage\n"
                      "package q;\n"
                      "  typedef enum { ORIGINAL = 3, FALSE } teeth_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import p::*;\n"
                      "  import q::teeth_t, q::ORIGINAL, q::FALSE;\n"
                      "  teeth_t myteeth;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    myteeth = FALSE;\n"
                      "    out = myteeth * 100 + ORIGINAL * 10 + TRUE;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            431u);
}

TEST(PackageScopeReferenceSim, ScopedEnumLiteralAssignedToAVariableOfItsType) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef enum { RED, GREEN, BLUE } color_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import p::*;\n"
                      "  color_t c1, c2;\n"
                      "  int i, j, out;\n"
                      "  initial begin\n"
                      "    c1 = BLUE;\n"
                      "    c2 = p::BLUE;\n"
                      "    i = p::GREEN;\n"
                      "    j = int'(p::BLUE);\n"
                      "    out = c1 * 1000 + c2 * 100 + i * 10 + j;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2212u);
}

TEST(PackageScopeReferenceSim, ScopedEnumLiteralAssignedWithoutAnImport) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef enum { RED, GREEN, BLUE } color_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  p::color_t c;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    c = p::BLUE;\n"
                      "    out = c;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2u);
}

TEST(PackageScopeReferenceSim, ScopedEnumLiteralMatchesAsACaseItem) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef enum { ONE = 1, TWO, THREE } num_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import p::*;\n"
                      "  num_t n;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    n = TWO;\n"
                      "    case (n)\n"
                      "      ONE: out = 1;\n"
                      "      p::TWO: out = 2;\n"
                      "      THREE: out = 3;\n"
                      "      default: out = 7;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2u);
}

TEST(PackageScopeReferenceSim, ScopedPackageClassVariableConstructedWithNew) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "  endclass\n"
                      "  C global_h;\n"
                      "endpackage\n"
                      "class Setter;\n"
                      "  function void go();\n"
                      "    p::global_h = new;\n"
                      "    p::global_h.v = 27;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static Setter s = new;\n"
                      "    p::global_h = new;\n"
                      "    p::global_h.v = 35;\n"
                      "    out = p::global_h.v * 10 + (p::global_h != null);\n"
                      "    p::global_h = null;\n"
                      "    s.go();\n"
                      "    out = out * 100 + p::global_h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            351u * 100u + 27u);
}

TEST(PackageScopeReferenceSim,
     ScopedPackageClassVariableConstructedWithItsSpecialization) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class G #(int N = 1);\n"
                      "    function int get_n();\n"
                      "      return N;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  G #(5) b;\n"
                      "  G d;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::b = new;\n"
                      "    p1::d = new;\n"
                      "    y = p1::b.get_n() * 10 + p1::d.get_n();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            51u);
}

TEST(PackageImportSim, WildcardImportInAFunctionBodyBindsItsNames) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  parameter int K = 8;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return K * five();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            40u);
}

TEST(PackageImportSim, ExplicitAndWildcardImportsInSeparateFunctionBodies) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  parameter int K = 8;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int K = 2;\n"
                      "  function int k(); import p::K; return K; endfunction\n"
                      "  function automatic int f();\n"
                      "    import p::*;\n"
                      "    return five();\n"
                      "  endfunction\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return K * five();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = k() * 1000 + f() * 100 + calc();\n"
                      "endmodule\n",
                      "out"),
            8540u);
}

TEST(PackageImportSim, WildcardImportInATaskBodyOutlivesItsDelay) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  parameter int K = 10;\n"
                      "  function int trip(int a); return a * 3; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  task automatic t(output int r);\n"
                      "    import p::*;\n"
                      "    #3 r = trip(K);\n"
                      "  endtask\n"
                      "  int r;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    t(r);\n"
                      "    out = r * 10 + $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            303u);
}

TEST(PackageImportSim, ExplicitlyExportedVariableReadThroughAWildcardImport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::x;\n"
                      "  export p1::x;\n"
                      "  int y = x + 1;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p2::*;\n"
                      "  int out;\n"
                      "  initial out = x * 10 + y;\n"
                      "endmodule\n",
                      "out"),
            67u);
}

TEST(PackageImportSim, StarStarExportedVariableReadThroughAWildcardImport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::x;\n"
                      "  export *::*;\n"
                      "  int y = x + 1;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p2::*;\n"
                      "  int out;\n"
                      "  initial out = x * 10 + y;\n"
                      "endmodule\n",
                      "out"),
            67u);
}

TEST(PackageImportSim, BodyImportedFunctionShadowsTheModulesOfTheSameName) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return five();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            5u);
}

TEST(PackageImportSim, BodyImportedFunctionShadowsTheInstancesOfTheSameName) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module child(output int o);\n"
                      "  function int five(); return 50; endfunction\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return five();\n"
                      "  endfunction\n"
                      "  initial o = calc();\n"
                      "endmodule\n"
                      "module top;\n"
                      "  int out;\n"
                      "  child u1(.o(out));\n"
                      "endmodule\n",
                      "out"),
            5u);
}

TEST(PackageImportSim, BodyWithoutImportCallsTheModulesFunctionOfTheSameName) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return five();\n"
                      "  endfunction\n"
                      "  function int plain(); return five(); endfunction\n"
                      "  int out;\n"
                      "  initial out = calc() * 100 + plain();\n"
                      "endmodule\n",
                      "out"),
            550u);
}

TEST(PackageScopeReferenceSim,
     PackageFunctionCallsAModuleFunctionItsPackageNeverNames) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int twice(); return base() * 2; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int base(); return 21; endfunction\n"
                      "  int out;\n"
                      "  initial out = p::twice();\n"
                      "endmodule\n",
                      "out"),
            42u);
}

TEST(PackageImportSim, WildcardImportedVariableReadByADeclarationInitializer) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int z = x;\n"
                      "  int y = p1::x;\n"
                      "  int out;\n"
                      "  initial out = z * 10 + y;\n"
                      "endmodule\n",
                      "out"),
            66u);
}

TEST(PackageImportSim,
     ExplicitlyImportedVariableReadByADeclarationInitializer) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::x;\n"
                      "  int z = x + 1;\n"
                      "endmodule\n",
                      "z"),
            7u);
}

TEST(PackageImportSim, VariableReachedByTwoExportPathsReadByAnInitializer) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::x;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "package p4;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "  int y = x;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p2::*;\n"
                      "  import p4::*;\n"
                      "  int z = x;\n"
                      "  int out;\n"
                      "  initial out = z * 10 + y;\n"
                      "endmodule\n",
                      "out"),
            66u);
}

TEST(PackageImportSim, AModulesOwnDeclarationShadowsAnImportInAnInitializer) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int x = 3;\n"
                      "  int z = x * 100 + p1::x;\n"
                      "endmodule\n",
                      "z"),
            306u);
}

TEST(PackageImportSim, ChildInstanceInitializerReadsItsOwnImport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "module reader;\n"
                      "  import p1::*;\n"
                      "  int z = x;\n"
                      "endmodule\n"
                      "module owner;\n"
                      "  import p1::*;\n"
                      "  int x = 3;\n"
                      "  int z = x;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  reader u();\n"
                      "  owner v();\n"
                      "  int out;\n"
                      "  initial out = u.z * 10 + v.z;\n"
                      "endmodule\n",
                      "out"),
            63u);
}

TEST(PackageImportSim, ExplicitlyImportedEnumLiteralInitializesADeclaration) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef enum { FALSE, TRUE } bool_t;\n"
                      "endpackage\n"
                      "package q;\n"
                      "  typedef enum { ORIGINAL = 3, FALSE } teeth_t;\n"
                      "endpackage\n"
                      "module top2;\n"
                      "  import p::*;\n"
                      "  import q::teeth_t, q::ORIGINAL, q::FALSE;\n"
                      "  teeth_t a = FALSE;\n"
                      "  bool_t b = TRUE;\n"
                      "  int out;\n"
                      "  initial out = a * 10 + b;\n"
                      "endmodule\n",
                      "out"),
            41u);
}

TEST(PackageScopeReferenceSim, PackageSemaphoreConstructedByScopedNew) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  semaphore t;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int a, b, y;\n"
                      "  initial begin\n"
                      "    p1::t = new(1);\n"
                      "    a = p1::t.try_get(1);\n"
                      "    b = p1::t.try_get(1);\n"
                      "    y = a * 10 + b;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

TEST(PackageScopeReferenceSim, ScopedNewKeyCountFillsThePackageSemaphore) {
  EXPECT_EQ(
      RunAndGet("package p1;\n"
                "  semaphore t;\n"
                "endpackage\n"
                "module top;\n"
                "  int y;\n"
                "  initial begin\n"
                "    p1::t = new(3);\n"
                "    y = p1::t.try_get(1) * 1000 + p1::t.try_get(1) * 100 +\n"
                "        p1::t.try_get(1) * 10 + p1::t.try_get(1);\n"
                "  end\n"
                "endmodule\n",
                "y"),
      1110u);
}

}  // namespace
