#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(InstanceScopeSimulation, ChildInitializerReadsOwnInstanceParameter) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module child #(parameter int P = 0);\n"
      "  int q = P;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(7)) u1();\n"
      "endmodule\n",
      f, "u1.q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 7u);
}

TEST(InstanceScopeSimulation,
     TwoInstancesInitializeFromTheirOwnParameterOverride) {
  SimFixture f;
  auto* q1 = RunAndFindVar(
      "module child #(parameter int P = 0);\n"
      "  int q = P;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(7)) u1();\n"
      "  child #(.P(9)) u2();\n"
      "endmodule\n",
      f, "u1.q");
  ASSERT_NE(q1, nullptr);
  auto* q2 = f.ctx.FindVariable("u2.q");
  ASSERT_NE(q2, nullptr);
  EXPECT_EQ(q1->value.ToUint64(), 7u);
  EXPECT_EQ(q2->value.ToUint64(), 9u);
}

TEST(InstanceScopeSimulation,
     ChildInitializerPrefersOwnDeclarationOverTopSameName) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] a = 8'hA5;\n"
      "  logic [7:0] b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a = 8'h3C;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xA5u);
}

TEST(InstanceScopeSimulation,
     ChildInitializerWithNoTopDeclarationReadsOwnVariable) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] a = 8'hA5;\n"
      "  logic [7:0] b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xA5u);
}

TEST(InstanceScopeSimulation, ChildEventInitializerAliasesOwnInstanceEvent) {
  SimFixture f;
  auto* e2 = RunAndFindVar(
      "module child;\n"
      "  event e1;\n"
      "  event e2 = e1;\n"
      "endmodule\n"
      "module top;\n"
      "  event e1;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.e2");
  ASSERT_NE(e2, nullptr);
  auto* e1 = f.ctx.FindVariable("u1.e1");
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e2, e1);
}

TEST(InstanceScopeSimulation, ChildDynArrayNewCopiesFromOwnInstanceSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  int src[] = '{4, 5};\n"
      "  int dst[] = new[2](src);\n"
      "endmodule\n"
      "module top;\n"
      "  int src[] = '{1, 2};\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* dst = f.ctx.FindQueue("u1.dst");
  ASSERT_NE(dst, nullptr);
  ASSERT_FALSE(dst->elements.empty());
  EXPECT_EQ(dst->elements[0].ToUint64(), 4u);
}

TEST(InstanceScopeSimulation,
     BareNameDoesNotReachTopVariableFromInsideInstance) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  int q = 7;\n"
      "endmodule\n"
      "module top;\n"
      "  int v = 3;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  f.ctx.SetLoweringInstancePrefix("u1.");
  EXPECT_EQ(f.ctx.FindVariable("v"), nullptr);
}

TEST(InstanceScopeSimulation, LocalNameStillResolvesUnderInstancePrefix) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  int q = 7;\n"
      "endmodule\n"
      "module top;\n"
      "  int v = 3;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  f.ctx.SetLoweringInstancePrefix("u1.");
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 7u);
}

TEST(InstanceScopeSimulation, HierarchicalNameStillClimbsPastModuleBoundary) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  int q = 7;\n"
      "endmodule\n"
      "module top;\n"
      "  int v = 3;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  f.ctx.SetLoweringInstancePrefix("u1.");
  auto* v = f.ctx.FindVariable("top.v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 3u);
}

TEST(InstanceScopeSimulation, BareParameterNameDoesNotReachTopParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  int q = 7;\n"
      "endmodule\n"
      "module top;\n"
      "  parameter int P = 3;\n"
      "  child u1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  f.ctx.SetLoweringInstancePrefix("u1.");
  EXPECT_EQ(f.ctx.FindVariable("P"), nullptr);
}

TEST(InstanceScopeSimulation, BlockLocalArrayShapeDoesNotOutliveItsBlock) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic got;\n"
      "  initial begin\n"
      "    a = 8'b1010_1010;\n"
      "    begin\n"
      "      int a [1:2];\n"
      "      a[1] = 5;\n"
      "    end\n"
      "    got = a[1];\n"
      "  end\n"
      "endmodule\n",
      f, "got");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InstanceScopeSimulation, ArrayFormalShapeDoesNotOutliveTheCall) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic got;\n"
      "  int src [1:2];\n"
      "  function int take(input int a [1:2]);\n"
      "    return a[1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a = 8'b1010_1010;\n"
      "    src[1] = 4; src[2] = 5;\n"
      "    got = take(src);\n"
      "    got = a[1];\n"
      "  end\n"
      "endmodule\n",
      f, "got");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(InstanceScopeSimulation, FunctionBareNameDoesNotReachItsCallersLocal) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int n = 7;\n"
                      "  int result;\n"
                      "  function automatic int read_n();\n"
                      "    return n;\n"
                      "  endfunction\n"
                      "  function automatic int caller();\n"
                      "    int n = 3;\n"
                      "    return read_n();\n"
                      "  endfunction\n"
                      "  initial result = caller();\n"
                      "endmodule\n",
                      "result"),
            7u);
}

TEST(InstanceScopeSimulation, StaticMethodBareStaticIsNotItsCallersLocal) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static C inst;\n"
                      "  int k = 4;\n"
                      "  static function void set(C c); inst = c; endfunction\n"
                      "  static function C get(); return inst; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  function automatic int first();\n"
                      "    C inst;\n"
                      "    C c = new;\n"
                      "    C::set(c);\n"
                      "    return C::get() == null ? 1 : C::get().k;\n"
                      "  endfunction\n"
                      "  function automatic int second();\n"
                      "    return C::get() == null ? 1 : C::get().k;\n"
                      "  endfunction\n"
                      "  initial result = first() * 10 + second();\n"
                      "endmodule\n",
                      "result"),
            44u);
}

TEST(InstanceScopeSimulation, AnAssignmentToANameDeclaredNowhereIsSkipped) {
  SimFixture f;
  auto* done = RunAndFindVar(
      "module t;\n"
      "  int done = 0;\n"
      "  initial begin\n"
      "    nosuch = 1;\n"
      "    done = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "done");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "undeclared identifier 'nosuch'", 4, "23.9"));
  ASSERT_NE(done, nullptr);
  EXPECT_EQ(done->value.ToUint64(), 1u);
}

TEST(ClassScopeStructureTypedefSim,
     AMemberNamedByTheClassTypedefTakesItsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef logic [7:0] nib_t;\n"
                       "class Box;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "  S s;\n"
                       "  function void show();\n"
                       "    s = 9'h1F5;\n"
                       "    $display(\"%0d %0d %0d\", $bits(s), s.x, s.y);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box b;\n"
                       "  initial begin b = new; b.show(); end\n"
                       "endmodule\n",
                       f),
            "5 10 1\n");
}

TEST(ClassScopeStructureTypedefSim,
     AMemberNamedByTheClassTypedefAloneTakesItsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Box;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "  S s;\n"
                       "  function void show();\n"
                       "    s = 9'h1F5;\n"
                       "    $display(\"%0d %0d %0d\", $bits(s), s.x, s.y);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box b;\n"
                       "  initial begin b = new; b.show(); end\n"
                       "endmodule\n",
                       f),
            "5 10 1\n");
}

TEST(ClassScopeStructureTypedefSim,
     AnInlineMemberTakesTheClassTypedefAndAPackageMemberItsOwn) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef logic [5:0] nib_t;\n"
                       "endpackage\n"
                       "typedef logic [7:0] nib_t;\n"
                       "class Box;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed {\n"
                       "    struct packed { nib_t a; } inner;\n"
                       "    p::nib_t z;\n"
                       "    logic y;\n"
                       "  } S;\n"
                       "  S s;\n"
                       "  function void show();\n"
                       "    s = {4'd10, 6'd51, 1'b1};\n"
                       "    $display(\"%0d %0d %0d %0d\", $bits(s), s.inner.a, "
                       "s.z, s.y);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box b;\n"
                       "  initial begin b = new; b.show(); end\n"
                       "endmodule\n",
                       f),
            "11 10 51 1\n");
}

TEST(ClassScopeTypedefNameSim, ATypedefNamedByAnotherTypedefInScopeTakesIt) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p;\n"
                 "  typedef logic [5:0] nib_t;\n"
                 "endpackage\n"
                 "typedef logic [7:0] nib_t;\n"
                 "class Base;\n"
                 "  typedef logic [2:0] tri_t;\n"
                 "endclass\n"
                 "class Box extends Base;\n"
                 "  typedef logic [3:0] nib_t;\n"
                 "  typedef nib_t pair_t;\n"
                 "  typedef p::nib_t pkg_t;\n"
                 "  typedef tri_t three_t;\n"
                 "endclass\n"
                 "module t;\n"
                 "  initial $display(\"%0d %0d %0d\", $bits(Box::pair_t), "
                 "$bits(Box::pkg_t), $bits(Box::three_t));\n"
                 "endmodule\n",
                 f),
      "4 6 3\n");
}

TEST(ClassScopeTypedefNameSim, ATypedefNamedByAnotherClassTypedefAloneTakesIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Box;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef nib_t pair_t;\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial $display(\"%0d\", $bits(Box::pair_t));\n"
                       "endmodule\n",
                       f),
            "4\n");
}

TEST(PackageScopeStructureTypedefSim, AMemberNamedByThePackageTypedefTakesIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef class C;\n"
                       "  class C; endclass\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "  typedef struct packed {\n"
                       "    struct packed { nib_t a; } inner;\n"
                       "    logic y;\n"
                       "  } T;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  typedef logic [7:0] nib_t;\n"
                       "  initial $display(\"%0d %0d\", $bits(p::S), "
                       "$bits(p::T));\n"
                       "endmodule\n",
                       f),
            "5 5\n");
}

TEST(PackageScopeStructureTypedefSim,
     AMemberNamedByThePackageTypedefAloneTakesIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  initial $display(\"%0d\", $bits(p::S));\n"
                       "endmodule\n",
                       f),
            "5\n");
}

TEST(ImportedStructureTypedefSim, ANamedImportKeepsThePackagesMemberType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  import p::S;\n"
                       "  typedef logic [7:0] nib_t;\n"
                       "  S s;\n"
                       "  initial $display(\"%0d\", $bits(s));\n"
                       "endmodule\n",
                       f),
            "5\n");
}

TEST(ImportedStructureTypedefSim, AWildcardImportKeepsThePackagesMemberType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  import p::*;\n"
                       "  typedef logic [7:0] nib_t;\n"
                       "  S s;\n"
                       "  initial $display(\"%0d\", $bits(s));\n"
                       "endmodule\n",
                       f),
            "5\n");
}

TEST(ImportedStructureTypedefSim, ANamedImportAloneKeepsThePackagesMemberType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  import p::S;\n"
                       "  S s;\n"
                       "  initial $display(\"%0d\", $bits(s));\n"
                       "endmodule\n",
                       f),
            "5\n");
}

TEST(ParameterizedClassStructureTypedefSim, AMemberTakesTheClassTypedef) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Box #(int W = 2);\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t [W-1:0] x; logic y; } "
                       "S;\n"
                       "  S s;\n"
                       "  function void show();\n"
                       "    s = 9'h1A5;\n"
                       "    $display(\"%0d %0d %0d\", $bits(s), s.x, s.y);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box #() b;\n"
                       "  initial begin b = new; b.show(); end\n"
                       "endmodule\n",
                       f),
            "9 210 1\n");
}

TEST(ParameterizedClassStructureTypedefSim,
     AMemberTakesTheClassTypedefOverTheUnits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef logic [5:0] nib_t;\n"
                       "class Box #(int W = 2);\n"
                       "  typedef logic [7:0] byte_t;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef struct packed { nib_t [W-1:0] x; logic y; } "
                       "S;\n"
                       "  S s;\n"
                       "  function void show();\n"
                       "    s = 9'h1A5;\n"
                       "    $display(\"%0d %0d %0d\", $bits(s), s.x, s.y);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box #() b;\n"
                       "  initial begin b = new; b.show(); end\n"
                       "endmodule\n",
                       f),
            "9 210 1\n");
}

TEST(ParameterizedClassStructureTypedefSim,
     AMemberTakesTheClassTypedefUnderEachSpecialization) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Box #(int W = 2);\n"
                       "  typedef logic [W-1:0] w_t;\n"
                       "  typedef struct packed { w_t x; logic y; } S;\n"
                       "  S s;\n"
                       "  function int width(); return $bits(s); endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box #(3) a;\n"
                       "  Box #(5) b;\n"
                       "  initial begin\n"
                       "    a = new; b = new;\n"
                       "    $display(\"%0d %0d\", a.width(), b.width());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "4 6\n");
}

TEST(ParameterizedClassStructureTypedefSim, AMemberTakesAnInheritedTypedef) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Base;\n"
                       "  int k;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "endclass\n"
                       "class Der #(int W = 2) extends Base;\n"
                       "  typedef struct packed { nib_t [W-1:0] x; logic y; } "
                       "S;\n"
                       "  S s;\n"
                       "  function int width(); return $bits(s); endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Der #() d;\n"
                       "  initial begin d = new; $display(\"%0d\", d.width()); "
                       "end\n"
                       "endmodule\n",
                       f),
            "9\n");
}

TEST(ParameterizedClassStructureTypedefSim,
     AMemberNamedOutsideTheClassKeepsItsType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef logic [2:0] t3;\n"
                       "endpackage\n"
                       "typedef logic [4:0] t5;\n"
                       "class Box #(int W = 2);\n"
                       "  typedef struct packed { p::t3 a; t5 b; logic [W-1:0] "
                       "c; } S;\n"
                       "  S s;\n"
                       "  function int width(); return $bits(s); endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box #() b;\n"
                       "  initial begin b = new; $display(\"%0d\", b.width()); "
                       "end\n"
                       "endmodule\n",
                       f),
            "10\n");
}

}  // namespace
