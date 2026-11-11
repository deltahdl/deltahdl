#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ParameterizedScopeResolutionSim, BothClassAndLocalParamsReadable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(parameter int p = 10);\n"
      "  parameter int q = 20;\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#()::p;\n"
      "    b = C#()::q;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10u}, {"b", 20u}});
}

TEST(ParameterizedScopeResolutionSim, TwoSpecializationsReturnDifferentValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class C #(parameter int W = 8);\n"
      "  static function int get_w;\n"
      "    get_w = W;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#(3)::get_w();\n"
      "    b = C#(7)::get_w();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 3u}, {"b", 7u}});
}

TEST(ParameterizedScopeResolutionSim,
     SpecificSpecializationValueAccessUsesOverride) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(parameter int p = 1);\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#(3)::p;\n"
      "    b = C#(7)::p;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 3u}, {"b", 7u}});
}

TEST(ParameterizedScopeResolutionSim,
     OutOfBlockMethodTakesValueFromCallSiteSpecialization) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(parameter int p = 1);\n"
      "  extern static function int f();\n"
      "endclass\n"
      "function int C::f();\n"
      "  return p;\n"
      "endfunction\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#()::f();\n"
      "    b = C#(5)::f();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 5u}});
}

TEST(ParameterizedScopeResolutionSim,
     ScopeResolvedParamInMethodTracksActiveSpecialization) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class C #(parameter int p = 1);\n"
      "  static function int f();\n"
      "    return p + C::p;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#()::f();\n"
      "    b = C#(5)::f();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 2u}, {"b", 10u}});
}

TEST(ParameterizedScopeResolutionSim, SpecializationArgumentFromLocalparam) {
  EXPECT_EQ(RunAndGet("class C #(parameter int p = 1);\n"
                      "endclass\n"
                      "module t;\n"
                      "  localparam int K = 6;\n"
                      "  int result;\n"
                      "  initial result = C#(K)::p;\n"
                      "endmodule\n",
                      "result"),
            6u);
}

TEST(ParameterizedScopeResolutionSim,
     SpecializationArgumentFromModuleParameter) {
  EXPECT_EQ(RunAndGet("class C #(parameter int p = 1);\n"
                      "endclass\n"
                      "module t #(parameter int W = 9);\n"
                      "  int result;\n"
                      "  initial result = C#(W)::p;\n"
                      "endmodule\n",
                      "result"),
            9u);
}

TEST(ParameterizedScopeResolutionSim,
     SpecializationLeavesLocalParameterUnchanged) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(parameter int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#(3)::p;\n"
      "    b = C#(3)::q;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 3u}, {"b", 5u}});
}

TEST(ParameterizedScopeResolutionSim, NamedSpecializationOverrideResolves) {
  EXPECT_EQ(RunAndGet("class C #(parameter int p = 1);\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C#(.p(3))::p;\n"
                      "endmodule\n",
                      "result"),
            3u);
}

TEST(ParameterizedScopeResolutionSim,
     DefaultScopeAccessFoldsAsConstantExpression) {
  EXPECT_EQ(RunAndGet("class C #(parameter int p = 3);\n"
                      "endclass\n"
                      "module t;\n"
                      "  localparam int W = C#()::p;\n"
                      "  int result;\n"
                      "  initial result = W;\n"
                      "endmodule\n",
                      "result"),
            3u);
}

TEST(ParameterizedScopeResolutionSim,
     SpecificSpecializationFoldsInConstantExpression) {
  EXPECT_EQ(RunAndGet("class C #(parameter int p = 1);\n"
                      "endclass\n"
                      "module t;\n"
                      "  localparam int W = C#(4)::p;\n"
                      "  int result;\n"
                      "  initial result = W;\n"
                      "endmodule\n",
                      "result"),
            4u);
}

TEST(ParameterizedScopeResolutionSim,
     UnadornedScopeInsideClassSelectsParameterOverLocal) {
  EXPECT_EQ(RunAndGet("class C #(parameter int p = 1);\n"
                      "  static function int g();\n"
                      "    int p = 99;\n"
                      "    return C::p;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C#()::g();\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ParameterizedScopeResolutionSim,
     ScopeResolutionThroughATypedefOfTheDefaultSpecialization) {
  EXPECT_EQ(RunAndGet("class C #(int p = 1);\n"
                      "  parameter int q = 5;\n"
                      "endclass\n"
                      "module t;\n"
                      "  typedef C T;\n"
                      "  int result;\n"
                      "  initial result = T::p * 100 + T::q * 10 + C#()::p;\n"
                      "endmodule\n",
                      "result"),
            151u);
}

TEST(ParameterizedScopeResolutionSim,
     StaticPropertyThroughATypedefOfAPlainClass) {
  EXPECT_EQ(RunAndGet("class K;\n"
                      "  static int n = 6;\n"
                      "endclass\n"
                      "module t;\n"
                      "  typedef K KT;\n"
                      "  int result;\n"
                      "  initial result = KT::n + 30;\n"
                      "endmodule\n",
                      "result"),
            36u);
}

TEST(ParameterizedScopeResolutionSim,
     BitsOfATypeParameterInAStaticMethodOfASpecialization) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class Box #(type T = int);\n"
                      "    static function int bits(); return $bits(T);\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import p::*;\n"
                      "  int out;\n"
                      "  initial out = Box#(byte)::bits() * 10000 +\n"
                      "                p::Box#(byte)::bits() * 100 +\n"
                      "                p::Box#(shortint)::bits();\n"
                      "endmodule\n",
                      "out"),
            8u * 10000u + 8u * 100u + 16u);
}

TEST(ParameterizedScopeResolutionSim,
     BitsOfATypeParameterInAStaticMethodOfTheDefaultSpecialization) {
  EXPECT_EQ(RunAndGet("class Box #(type T = byte);\n"
                      "  static function int bits(); return $bits(T);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial out = Box#()::bits() * 100 +\n"
                      "                Box#(shortint)::bits();\n"
                      "endmodule\n",
                      "out"),
            8u * 100u + 16u);
}

TEST(ParameterizedScopeResolutionSim,
     BitsOfARangedTypedefOrNamedTypeActualInAStaticMethod) {
  EXPECT_EQ(RunAndGet("class Box #(type T = int);\n"
                      "  static function int bits(); return $bits(T);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  typedef bit [19:0] word_t;\n"
                      "  int out;\n"
                      "  initial out = Box#(logic [11:0])::bits() * 10000 +\n"
                      "                Box#(int unsigned)::bits() * 100 +\n"
                      "                Box#(.T(word_t))::bits();\n"
                      "endmodule\n",
                      "out"),
            12u * 10000u + 32u * 100u + 20u);
}

TEST(ParameterizedScopeResolutionSim,
     BitsOfATypeParameterInAStaticTaskOfASpecialization) {
  EXPECT_EQ(RunAndGet("class Box #(type T = int);\n"
                      "  static task show(output int o);\n"
                      "    #1 o = $bits(T);\n"
                      "  endtask\n"
                      "endclass\n"
                      "module t;\n"
                      "  int a, b, out;\n"
                      "  initial begin\n"
                      "    Box#(shortint)::show(a);\n"
                      "    Box#()::show(b);\n"
                      "    out = a * 100 + b;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            16u * 100u + 32u);
}

TEST(ParameterizedScopeResolutionSim,
     BitsOfATypeParameterInAStaticTaskOfAPackageClassSpecialization) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class Box #(type T = int);\n"
                      "    static task show(output int o);\n"
                      "      #1 o = $bits(T);\n"
                      "    endtask\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int a, b, c, out;\n"
                      "  initial begin\n"
                      "    p::Box#(byte)::show(a);\n"
                      "    p::Box#(shortint)::show(b);\n"
                      "    p::Box#()::show(c);\n"
                      "    out = a * 10000 + b * 100 + c;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            8u * 10000u + 16u * 100u + 32u);
}

TEST(ParameterizedScopeResolutionSim,
     BareStaticCallInsideAStaticMethodOfASpecialization) {
  EXPECT_EQ(RunAndGet("class C #(int N = 1);\n"
                      "  static function int helper();\n"
                      "    return N * 2;\n"
                      "  endfunction\n"
                      "  static function int outer();\n"
                      "    return helper() + N;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = C#(5)::outer();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            15u);
}

TEST(ParameterizedScopeResolutionSim,
     BareInheritedStaticCallInsideAStaticMethodOfASpecialization) {
  EXPECT_EQ(RunAndGet("class Q;\n"
                      "  int n = 3;\n"
                      "  function int size(); return n; endfunction\n"
                      "endclass\n"
                      "class C #(type T = int);\n"
                      "  static function void m_get_q(ref Q q, input T obj);\n"
                      "    q = new;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class D #(type T = int) extends C#(T);\n"
                      "  static function int get_first(input T obj);\n"
                      "    Q q;\n"
                      "    m_get_q(q, obj);\n"
                      "    return q == null ? 7 : q.size();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Iter #(type T = int);\n"
                      "  function int first();\n"
                      "    return D#(T)::get_first(0);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Iter#(int) it = new;\n"
                      "    result = it.first();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3u);
}

TEST(ParameterizedScopeResolutionSim, StaticPropertyReadsItsSpecialization) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class vector #(int size = 1);\n"
      "  static int count = 0;\n"
      "  function new(); count++; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  vector #(1) x1 = new, y1 = new;\n"
      "  vector #(4) x4 = new;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = vector#(1)::count;\n"
      "    b = vector#(4)::count;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 2u}, {"b", 1u}});
}

TEST(ParameterizedScopeResolutionSim,
     StaticInitializerRunsForTheScopeNamedSpecialization) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class V #(int size = 1);\n"
      "  static const int W = size;\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = V#(4)::W;\n"
      "    b = V#(8)::W;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 4u}, {"b", 8u}});
}

TEST(ParameterizedScopeResolutionSim,
     StaticMethodCallRunsAgainstItsSpecialization) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class counter #(int size = 1);\n"
      "  static int count = 0;\n"
      "  function new(); count++; endfunction\n"
      "  static function int get(); return count; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  counter #(1) x1 = new, y1 = new;\n"
      "  counter #(4) x4 = new;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = counter#(1)::get();\n"
      "    b = counter#(4)::get();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 2u}, {"b", 1u}});
}

TEST(ParameterizedScopeResolutionSim,
     UnadornedScopeInsideClassReadsItsSpecializationStaticProperty) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class counter #(int size = 1);\n"
      "  static int count = 0;\n"
      "  function new(); count++; endfunction\n"
      "  static function int get(); return counter::count; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  counter #(1) x1 = new, y1 = new;\n"
      "  counter #(4) x4 = new;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = counter#(1)::get();\n"
      "    b = counter#(4)::get();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 2u}, {"b", 1u}});
}

TEST(ParameterizedScopeResolutionSim,
     TypeActualsOfAScopeNameTheSpecializationTheirTypesGive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(type T = int);\n"
      "  static int n;\n"
      "  static function void set(int v); n = v; endfunction\n"
      "  function int get(); return n; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C #(byte) cb = new;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    C#(byte)::set(1);\n"
      "    C#(shortint)::set(2);\n"
      "    a = C#(byte)::n;\n"
      "    b = C#(shortint)::n;\n"
      "    c = cb.get();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 1u}});
}

TEST(ParameterizedScopeResolutionSim,
     TypeParameterOfTheRunningClassInAScopeListIsItsActual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Box #(type T = int);\n"
      "  static function int w(); return $bits(T); endfunction\n"
      "endclass\n"
      "class Reg #(type T = int);\n"
      "  static function int sw(); return Box#(T)::w(); endfunction\n"
      "  function int iw(); return Box#(T)::w(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  Reg #(shortint) r = new;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = Reg#(byte)::sw();\n"
      "    b = r.iw();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 8u}, {"b", 16u}});
}

TEST(ParameterizedScopeResolutionSim,
     DefaultSpecializationsTypedefNamesTheSpecializationOfItsDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class R #(type T = int);\n"
      "  static int id;\n"
      "endclass\n"
      "class Own #(type T = int);\n"
      "  typedef R #(T) rsrc_t;\n"
      "  function int td(); return rsrc_t::id; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  Own #(int) o = new;\n"
      "  Own #(byte) b = new;\n"
      "  int a, c;\n"
      "  initial begin\n"
      "    R#(int)::id = 7;\n"
      "    R#(byte)::id = 9;\n"
      "    a = o.td();\n"
      "    c = b.td();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 7u}, {"c", 9u}});
}

TEST(ParameterizedScopeResolutionSim,
     StaticTaskOfASpecializationReadsItsOwnStaticProperty) {
  EXPECT_EQ(RunAndGet("class C #(int N = 1);\n"
                      "  static int s = N;\n"
                      "  static task t(output int r); r = s; endtask\n"
                      "endclass\n"
                      "module t;\n"
                      "  int a, b, out;\n"
                      "  initial begin\n"
                      "    C#(4)::t(a);\n"
                      "    C#(7)::t(b);\n"
                      "    out = a * 100 + b;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            4u * 100u + 7u);
}

TEST(ParameterizedScopeResolutionSim,
     DefaultSpecializationStaticInitializerReadsTheDefault) {
  EXPECT_EQ(RunAndGet("class P #(int N = 3);\n"
                      "  static int s = N;\n"
                      "  static int k = N * 10;\n"
                      "  function int ird(); return s; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  P p;\n"
                      "  P #(3) q;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    p = new; q = new;\n"
                      "    out = P#()::s * 1000 + p.ird() * 100 + q.s * 10 +\n"
                      "          P#()::k / 10;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            3333u);
}

TEST(ParameterizedScopeResolutionSim, LocalParameterReadThroughAHandle) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module top;\n"
      "  typedef C T;\n"
      "  T obj = new();\n"
      "  int u = obj.q;\n"
      "  int r1;\n"
      "  initial r1 = u;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 5u}});
}

TEST(ParameterizedScopeResolutionSim,
     SpecializationParameterIsReadWhereNoConstantIsAsked) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Z #(int P); parameter int K = 2; localparam int N = P * 2; "
      "endclass\n"
      "class ZD #(int P = 1); parameter int K = 2; localparam int N = P * 2; "
      "endclass\n"
      "module child #(parameter int Q = 0);\n"
      "endmodule\n"
      "module top;\n"
      "  localparam int B1 = Z#(3)::K;\n"
      "  localparam int B2 = ZD#(3)::N;\n"
      "  logic [Z#(3)::P:0] v;\n"
      "  if (Z#(3)::P == 3) begin : g\n"
      "    localparam int G = 1;\n"
      "  end\n"
      "  child #(.Q(Z#(3)::N)) c();\n"
      "  int x = 3;\n"
      "  int r1, r2, r3, r4, r5, r6;\n"
      "  initial begin\n"
      "    r1 = B1; r2 = B2; r3 = $bits(v); r4 = g.G; r5 = c.Q;\n"
      "    case (x) Z#(3)::P: r6 = 1; default: r6 = 9; endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"r1", 2u}, {"r2", 6u}, {"r3", 4u}, {"r4", 1u}, {"r5", 6u}, {"r6", 1u}});
}

TEST(ParameterizedScopeResolutionSim,
     DISABLED_SpecializationParameterWithoutDefaultIsAConstantEverywhere) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Z #(int P); parameter int K = 2; localparam int N = P * 2; "
      "endclass\n"
      "class VN #(int a, int size); localparam int N = size * 2 + a; endclass\n"
      "class TD #(type T = int, int size = 1); parameter int K = 2; localparam "
      "int N = size * 2; endclass\n"
      "class TN #(type T, int size); parameter int K = 2; localparam int N = "
      "size * 2; endclass\n"
      "localparam int U1 = Z#(3)::N;\n"
      "package pk;\n"
      "  class PZ #(int P); localparam int N = P * 2; endclass\n"
      "  localparam int P1 = PZ#(3)::N;\n"
      "endpackage\n"
      "class HC;\n"
      "  localparam int H1 = Z#(3)::N;\n"
      "endclass\n"
      "interface ifc;\n"
      "  localparam int I1 = Z#(3)::N;\n"
      "endinterface\n"
      "module sub #(parameter int PV = Z#(3)::P);\n"
      "endmodule\n"
      "module top;\n"
      "  ifc i();\n"
      "  sub s();\n"
      "  localparam int A1 = Z#(3)::P;\n"
      "  localparam int A2 = Z#(3)::N;\n"
      "  localparam int A3 = Z#(.P(5))::N;\n"
      "  localparam int A4 = VN#(1, 4)::N;\n"
      "  localparam int A5 = TD#(byte, 4)::K;\n"
      "  localparam int A6 = TD#(byte, 4)::N;\n"
      "  localparam int A7 = TN#(byte, 4)::K;\n"
      "  localparam int A8 = TN#(byte, 4)::N;\n"
      "  localparam int A9 = TN#(byte, 4)::size;\n"
      "  if (1) begin : g\n"
      "    localparam int G1 = Z#(3)::N;\n"
      "  end\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, "
      "r15;\n"
      "  initial begin\n"
      "    r1 = A1; r2 = A2; r3 = A3; r4 = A4; r5 = A5; r6 = A6; r7 = A7; r8 = "
      "A8; r9 = A9;\n"
      "    r10 = U1; r11 = pk::P1; r12 = HC::H1; r13 = i.I1; r14 = s.PV; r15 = "
      "g.G1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 3u},
                    {"r2", 6u},
                    {"r3", 10u},
                    {"r4", 9u},
                    {"r5", 2u},
                    {"r6", 8u},
                    {"r7", 2u},
                    {"r8", 8u},
                    {"r9", 4u},
                    {"r10", 6u},
                    {"r11", 6u},
                    {"r12", 6u},
                    {"r13", 6u},
                    {"r14", 3u},
                    {"r15", 6u}});
}

TEST(ParameterizedScopeResolutionSim,
     DISABLED_MemberIsReachedThroughASpecializationsStaticHandle) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; int x = 7; endclass\n"
      "class S #(int N = 1); static C s; endclass\n"
      "module m;\n"
      "  C o;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    o = new;\n"
      "    S#(2)::s = o;\n"
      "    r1 = S#(2)::s.x;\n"
      "    S#(2)::s.x = 9;\n"
      "    r2 = o.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 7u}, {"r2", 9u}});
}

TEST(ParameterizedScopeResolutionSim,
     SpecializationsStaticHandleCopiedToALocalReachesItsObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; int x = 7; endclass\n"
      "class S #(int N = 1); static C s; endclass\n"
      "class T; static C s; endclass\n"
      "module m;\n"
      "  C o, l;\n"
      "  int r1, r2, r3;\n"
      "  initial begin\n"
      "    o = new;\n"
      "    S#(2)::s = o;\n"
      "    l = S#(2)::s;\n"
      "    r1 = l.x;\n"
      "    T::s = o;\n"
      "    r2 = T::s.x;\n"
      "    T::s.x = 9;\n"
      "    r3 = o.x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 7u}, {"r2", 7u}, {"r3", 9u}});
}

}  // namespace
