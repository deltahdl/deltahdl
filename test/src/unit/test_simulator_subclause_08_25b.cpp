#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

// §8.25 (printed page 204 of IEEE 1800-2023): a specialization is a generic
// class combined with one set of actual parameter values, and each
// specialization has its own set of static member variables -- a static shared
// across specializations has to be declared in a nonparameterized base class
// instead. The clause's own `vector #(int size = 1)` example says it in terms:
// each specialization has its own copy of the static `count`, and a method
// reads the copy of the specialization it runs in.
//
// The cases here run the whole pipeline on source text, because the defect is
// invisible to a case that builds the types by hand: SpecializationsHaveIndep
// endentStaticMembers in the a half of this family registers two unrelated
// ClassTypeInfo values, one named Vec_8 and one Vec_16, and finds their static
// maps independent, which they are by construction. What is wrong is upstream
// of that -- one ClassTypeInfo is lowered per class declaration and serves
// every specialization, so the two share one map -- and only a parameterized
// class declared, specialized and run can show it.

namespace {

// §8.25: two `vector #(1)` objects and one `vector #(4)` object. The counts
// discriminate: with one shared static the three constructions leave 3 for
// both reads, and with a static per specialization they leave 2 and 1.
TEST(ClassSim, StaticPropertyCountsPerSpecialization) {
  SimFixture f;
  auto out = RunCapture(
      "class vector #(int size = 1);\n"
      "  bit [size-1:0] a;\n"
      "  static int count = 0;\n"
      "  function new(); count++; endfunction\n"
      "  function int get(); return count; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  vector #(1) x1 = new, y1 = new;\n"
      "  vector #(4) x4 = new;\n"
      "  initial begin\n"
      "    $display(\"c1 %0d\", x1.get());\n"
      "    $display(\"c4 %0d\", x4.get());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "c1 2\nc4 1\n");
}

// §8.25 with §8.9 (printed 186): a static property's initializer is evaluated
// once for the specialization it belongs to, so a static initialized from the
// class's value parameter reads that specialization's actual. The two widths
// discriminate from each other and from the 0 a single shared copy gives.
TEST(ClassSim, StaticInitializerReadsItsSpecializationParameter) {
  SimFixture f;
  auto out = RunCapture(
      "class V #(int size = 1);\n"
      "  static const int W = size;\n"
      "endclass\n"
      "module t;\n"
      "  V #(4) v4 = new;\n"
      "  V #(8) v8 = new;\n"
      "  initial begin\n"
      "    $display(\"w4 %0d\", v4.W);\n"
      "    $display(\"w8 %0d\", v8.W);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "w4 4\nw8 8\n");
}

// §8.25 (printed page 204 of IEEE 1800-2023) with §8.25.1 (printed 205): a
// specialization is a distinct type, and where the extends clause names one of
// the class's own type parameters -- `class D #(type B = P) extends B;` -- the
// class each specialization extends is the one that specialization's actual
// binds the parameter to, the default the declaration wrote being the base of
// the default specialization alone. Two bases whose `who()` answer differently
// discriminate: taking the base from the default leaves both reads at P's 1,
// and extending the class each actual names leaves 1 and 2.
TEST(ClassSim, SpecializationExtendsTheBaseItsOwnActualNames) {
  SimFixture f;
  auto out = RunCapture(
      "class P;\n"
      "  function int who(); return 1; endfunction\n"
      "endclass\n"
      "class Q;\n"
      "  function int who(); return 2; endfunction\n"
      "endclass\n"
      "class D #(type B = P) extends B;\n"
      "endclass\n"
      "module t;\n"
      "  D #(P) dp = new;\n"
      "  D #(Q) dq = new;\n"
      "  initial begin\n"
      "    $display(\"p %0d\", dp.who());\n"
      "    $display(\"q %0d\", dq.who());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "p 1\nq 2\n");
}

// §8.25 (printed page 204 of IEEE 1800-2023) with §6.18: a typedef names the
// type its declaration writes, and what `typedef V#(4) t4;` writes is a
// specialization -- a generic class together with one set of actual parameter
// values -- rather than the generic class, which §8.25 says is no type at all.
// The name therefore reaches the static member variables of that one
// specialization. Two typedefs of one class discriminate: binding the alias to
// the declaration's own type, which §8.25.1 makes the default specialization,
// leaves both reads at the default's 1, and binding each to the specialization
// its own actuals name leaves 4 and 8.
TEST(ClassSim, ClassScopeTypedefOfASpecializationNamesThatSpecialization) {
  SimFixture f;
  auto out = RunCapture(
      "class V #(int size = 1);\n"
      "  static const int W = size;\n"
      "endclass\n"
      "class Holder;\n"
      "  typedef V#(4) t4;\n"
      "  typedef V#(8) t8;\n"
      "  function int a(); return t4::W; endfunction\n"
      "  function int b(); return t8::W; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  Holder h = new;\n"
      "  initial begin\n"
      "    $display(\"a %0d\", h.a());\n"
      "    $display(\"b %0d\", h.b());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a 4\nb 8\n");
}

// §8.25 (printed page 204 of IEEE 1800-2023): the actuals belong to the
// specialization, which is the type, rather than to the declaration of the
// variable each object is constructed on. Where the name the `new` is written
// against is a typedef of a specialization, that declaration writes no
// `#(...)` list of its own, so the actuals have to come from the type: D's
// extends clause passes its own P to C's T, and the P the object stands under
// is the one its specialization binds. Two typedefs of one class discriminate:
// falling back to the parameter's default leaves both reads at real's 64, and
// taking each specialization's own actual leaves integer's 32 and shortint's
// 16.
TEST(ClassSim, ConstructedThroughATypedefTheBaseTakesTheSpecializationsActual) {
  SimFixture f;
  auto out = RunCapture(
      "class C #(type T = real);\n"
      "  T x;\n"
      "  function int w(); return $bits(x); endfunction\n"
      "endclass\n"
      "class D #(type P = real) extends C #(P);\n"
      "endclass\n"
      "class Holder;\n"
      "  typedef D#(integer) di;\n"
      "  typedef D#(shortint) ds;\n"
      "  function int a(); di u = new; return u.w(); endfunction\n"
      "  function int b(); ds v = new; return v.w(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  Holder h = new;\n"
      "  initial begin\n"
      "    $display(\"a %0d\", h.a());\n"
      "    $display(\"b %0d\", h.b());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a 32\nb 16\n");
}

}  // namespace
