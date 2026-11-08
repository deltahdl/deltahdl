#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackageImportSim, WildcardImportParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  parameter int VAL = 99;\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::*;\n"
      "  logic [7:0] x;\n"
      "  initial x = VAL;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 99u);
}

TEST(PackageScopeReferenceSim, PackageScopeParamResolves) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  parameter int WIDTH = 16;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [31:0] y;\n"
      "  initial y = pkg::WIDTH;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 16u);
}

TEST(PackageImportSim, WildcardImportEnumLiteralEvaluates) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  typedef enum { LOW, MID, HIGH } level_t;\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::*;\n"
      "  level_t sel;\n"
      "  logic [31:0] y;\n"
      "  initial begin\n"
      "    sel = HIGH;\n"
      "    y = sel;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 2u);
}

TEST(PackageImportSim, ExplicitImportParameter) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  parameter int VAL = 77;\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::VAL;\n"
      "  logic [31:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 77u);
}

TEST(PackageScopeReferenceSim, PackageScopeLocalparamResolves) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  localparam int W = 24;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [31:0] y;\n"
      "  initial y = pkg::W;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 24u);
}

TEST(PackageImportSim, ExplicitImportFunctionCalledUnqualified) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  function automatic int scale(int a);\n"
      "    return a * 5;\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::scale;\n"
      "  logic [31:0] y;\n"
      "  initial y = scale(4);\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 20u);
}

TEST(PackageImportSim, InstantiatedModuleReadsImportedParameter) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "package pkg;\n"
      "  parameter int VAL = 77;\n"
      "endpackage\n"
      "module child;\n"
      "  import pkg::VAL;\n"
      "  logic [31:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n"
      "module top;\n"
      "  import pkg::VAL;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 77u);
}

TEST(PackageImportSim, ChildAloneImportsParameterAndReadsItUnqualified) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "package pkg;\n"
      "  parameter int VAL = 77;\n"
      "endpackage\n"
      "module child;\n"
      "  import pkg::VAL;\n"
      "  logic [31:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n"
      "module top;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 77u);
}

TEST(PackageImportSim,
     ChildAloneWildcardImportsParameterAndReadsItUnqualified) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "package pkg;\n"
      "  parameter int VAL = 77;\n"
      "endpackage\n"
      "module child;\n"
      "  import pkg::*;\n"
      "  logic [31:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n"
      "module top;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 77u);
}

TEST(PackageImportSim, ChildAloneImportsFunctionAndCallsItUnqualified) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "package pkg;\n"
      "  function int scale(int x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "endpackage\n"
      "module child;\n"
      "  import pkg::scale;\n"
      "  logic [31:0] y;\n"
      "  initial y = scale(10);\n"
      "endmodule\n"
      "module top;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 20u);
}

TEST(PackageImportSim,
     TwoInstancesImportLikeNamedParametersFromDifferentPackages) {
  SimFixture f;
  auto* ya = RunAndFindVar(
      "package pkga;\n"
      "  parameter int VAL = 11;\n"
      "endpackage\n"
      "package pkgb;\n"
      "  parameter int VAL = 22;\n"
      "endpackage\n"
      "module childa;\n"
      "  import pkga::VAL;\n"
      "  logic [31:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n"
      "module childb;\n"
      "  import pkgb::VAL;\n"
      "  logic [31:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n"
      "module top;\n"
      "  childa u1();\n"
      "  childb u2();\n"
      "endmodule\n",
      f, "u1.y");
  ASSERT_NE(ya, nullptr);
  EXPECT_EQ(ya->value.ToUint64(), 11u);
  auto* yb = f.ctx.FindVariable("u2.y");
  ASSERT_NE(yb, nullptr);
  EXPECT_EQ(yb->value.ToUint64(), 22u);
}

TEST(PackageScopeReferenceSim, PackageScopedTypedefSizesBlockLocal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [3:0] nib_t;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [31:0] w, b;\n"
      "  initial begin\n"
      "    pkg::nib_t v;\n"
      "    v = -1;\n"
      "    w = v;\n"
      "    b = $bits(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("w")->value.ToUint64(), 15u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 4u);
}

TEST(PackageScopeReferenceSim, PackageScopedTypedefKeepsBlockLocalSigned) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  typedef byte sb_t;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [31:0] y;\n"
      "  initial begin\n"
      "    pkg::sb_t s;\n"
      "    s = -1;\n"
      "    y = (s < 0) ? 1 : 2;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 1u);
}

TEST(PackageScopeReferenceSim, PackageScopedTypedefMakesBlockLocalAString) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  typedef string str_t;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [31:0] n;\n"
      "  initial begin\n"
      "    pkg::str_t s;\n"
      "    s = \"abcde\";\n"
      "    n = s.len();\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(val, 5u);
}

TEST(PackageImportSim, WildcardImportedClassStaticMethodCalledByBareName) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class plain_t;\n"
                      "    static function int get();\n"
                      "      return 8;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import p::*;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = plain_t::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            8u);
}

TEST(PackageImportSim, UnitScopeWildcardImportBindsPackageClass) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class plain_t;\n"
                      "    static function int get();\n"
                      "      return 8;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "import p::*;\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = plain_t::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            8u);
}

TEST(PackageScopeReferenceSim, PackageQualifiedClassStaticMethodCall) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class pk_t;\n"
                      "    static function int get();\n"
                      "      return 9;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = p::pk_t::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            9u);
}

TEST(PackageScopeReferenceSim, UnitClassKeepsNameOverImportedPackageClass) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class same_t;\n"
                      "    static function int get();\n"
                      "      return 9;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "import p::*;\n"
                      "class same_t;\n"
                      "  static function int get();\n"
                      "    return 8;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = same_t::get() * 10 + p::same_t::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            89u);
}

TEST(PackageScopeReferenceSim, PackageQualifiedHandleMethodCall) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v = 3;\n"
                      "    function int m();\n"
                      "      return v * 7;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    y = p1::h.m();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            21u);
}

TEST(PackageScopeReferenceSim, PackageQualifiedHandleTaskEnableWritesProperty) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "    task t(int a);\n"
                      "      v = a;\n"
                      "    endtask\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    p1::h.t(5);\n"
                      "    y = p1::h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            5u);
}

TEST(PackageScopeReferenceSim, ExportedHandleMethodCallThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v = 3;\n"
                      "    function int m();\n"
                      "      return v * 7;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::h;\n"
                      "  export p1::h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p2::h = new;\n"
                      "    y = p2::h.m();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            21u);
}

TEST(PackageScopeReferenceSim, PackageQualifiedHandleMethodCallChained) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v = 3;\n"
                      "    function C self();\n"
                      "      return this;\n"
                      "    endfunction\n"
                      "    function int m();\n"
                      "      return v * 7;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    y = p1::h.self().m();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            21u);
}

TEST(PackageScopeReferenceSim,
     PackageQualifiedHandleParenthesisFreeMethodStatement) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "    function void m();\n"
                      "      v = 8;\n"
                      "    endfunction\n"
                      "    task t;\n"
                      "      v = v + 30;\n"
                      "    endtask\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    p1::h.m;\n"
                      "    p1::h.t;\n"
                      "    y = p1::h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            38u);
}

TEST(PackageScopeReferenceSim, PackageQualifiedHandleRandomize) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    rand bit [3:0] r;\n"
                      "    constraint c { r == 9; }\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    y = p1::h.randomize() * 10 + p1::h.r;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            19u);
}

TEST(PackageScopeReferenceSim,
     PackageQualifiedHandleRandModeAndConstraintMode) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    rand bit [3:0] r;\n"
                      "    constraint c { r == 9; }\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    y = p1::h.c.constraint_mode() * 10 + "
                      "p1::h.r.rand_mode();\n"
                      "    p1::h.c.constraint_mode(0);\n"
                      "    p1::h.rand_mode(0);\n"
                      "    y = y * 100 + p1::h.c.constraint_mode() * 10 + "
                      "p1::h.r.rand_mode();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1100u);
}

TEST(PackageScopeReferenceSim, PackageQualifiedHandleArrayElementRandMode) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    rand bit [3:0] arr[2];\n"
                      "    constraint c { arr[0] == 3; }\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y, held = 0;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    p1::h.arr[1] = 9;\n"
                      "    p1::h.arr[1].rand_mode(0);\n"
                      "    repeat (8) begin\n"
                      "      void'(p1::h.randomize());\n"
                      "      if (p1::h.arr[1] == 9) held++;\n"
                      "    end\n"
                      "    y = held * 1000 + p1::h.arr[0] * 100 + "
                      "p1::h.arr[1].rand_mode() * 10 + "
                      "p1::h.arr[0].rand_mode();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            8301u);
}

TEST(PackageScopeReferenceSim, PackageQualifiedQueuePushBackAndSize) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int q[$];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::q.push_back(4);\n"
                      "    p1::q.push_back(6);\n"
                      "    y = p1::q[1] * 10 + p1::q.size();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            62u);
}

TEST(PackageScopeReferenceSim, ImportedAndReExportedSemaphoreShareOneBucket) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  semaphore s = new(2);\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::s;\n"
                      "  export p1::s;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::s;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    s.get(1);\n"
                      "    p2::s.get(1);\n"
                      "    y = 10 + p1::s.try_get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

TEST(PackageScopeReferenceSim, PackageProcessHandleIsKilledAndReadsKilled) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  process proc;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int x = 0, y;\n"
                      "  initial begin\n"
                      "    fork\n"
                      "      begin\n"
                      "        p1::proc = process::self();\n"
                      "        #10 x = 99;\n"
                      "      end\n"
                      "    join_none\n"
                      "    #1;\n"
                      "    p1::proc.kill();\n"
                      "    #20;\n"
                      "    y = (p1::proc.status() == process::KILLED) * 10;\n"
                      "    y = y + (x == 0);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            11u);
}

TEST(PackageScopeReferenceSim, PackageProcessHandleAwaitsTermination) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  process proc;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int a = 0, y;\n"
                      "  initial begin\n"
                      "    fork\n"
                      "      begin\n"
                      "        p1::proc = process::self();\n"
                      "        #5 a = 1;\n"
                      "      end\n"
                      "    join_none\n"
                      "    #1;\n"
                      "    p1::proc.await();\n"
                      "    y = a;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1u);
}

TEST(PackageScopeReferenceSim,
     PackageFunctionInlineUnionFormalReadsANestedTypedefMember) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef struct { int a, b; } pair_t;\n"
                      "  function int f(union tagged { void None; pair_t Add; }"
                      " a);\n"
                      "    return a.Add.a * 10 + a.Add.b;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p::f(tagged Add '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            34u);
}

TEST(PackageScopeReferenceSim,
     PackageFunctionInlineUnionFormalResolvesAnotherPackagesQualifiedMember) {
  EXPECT_EQ(RunAndGet("package q;\n"
                      "  typedef struct { int a, b; } pair_t;\n"
                      "endpackage\n"
                      "package p;\n"
                      "  function int f(union tagged { void None; q::pair_t "
                      "Add; } a);\n"
                      "    return a.Add.a * 10 + a.Add.b;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p::f(tagged Add '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            34u);
}

TEST(PackageScopeReferenceSim,
     ModuleVariableInlineUnionResolvesAPackageQualifiedMember) {
  EXPECT_EQ(RunAndGet("package q;\n"
                      "  typedef struct { int a, b; } pair_t;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  union tagged { void None; q::pair_t Add; } v;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    v = tagged Add '{3, 4};\n"
                      "    y = v.Add.a * 10 + v.Add.b;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            34u);
}

}  // namespace
