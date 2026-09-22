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

// §8.25 (printed page 204 of IEEE 1800-2023): a parameterized class may extend
// a specialization of another, and `class D3 #(type P = real) extends C
// #(P);` binds C's T to P, so D3#(byte) extends C#(byte) -- a specialization,
// which §8.25 makes a type of its own with its own set of static member
// variables. A static property the base declares is therefore read, through a
// D#(byte) object, off B#(byte)'s copy, and through a D#(shortint) object off
// B#(shortint)'s. B#(byte) writes 5 into its own copy, and the reads
// discriminate: a specialization extending the base's declaration leaves both
// at 0, one copy shared by every specialization leaves both at 5, and the
// base each list names leaves 5 and 0.
TEST(ClassSim, SpecializationExtendsTheBaseSpecializationItsListNames) {
  SimFixture f;
  auto out = RunCapture(
      "class B #(type T = int);\n"
      "  static int n;\n"
      "  function void set(int v); n = v; endfunction\n"
      "endclass\n"
      "class D #(type T = int) extends B #(T);\n"
      "  function int get(); return n; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  B #(byte) b = new;\n"
      "  D #(byte) db = new;\n"
      "  D #(shortint) ds = new;\n"
      "  initial begin\n"
      "    b.set(5);\n"
      "    $display(\"b %0d\", db.get());\n"
      "    $display(\"s %0d\", ds.get());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "b 5\ns 0\n");
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

// §8.25 (printed page 204 of IEEE 1800-2023): a specialization is the generic
// class together with one set of actual parameter values, and the value
// parameters belong to it as the type parameters do, so a name that reaches
// the specialization reaches its values. `typedef V#(4) v4;` is such a name,
// and `v4 x = new` writes no `#(...)` of its own for the construction to read.
// Two typedefs of one class discriminate: the declaration's default leaves
// both reads at 1, and each specialization's own actual leaves 4 and 8.
TEST(ClassSim, ConstructedThroughATypedefTheValueParameterIsTheActual) {
  SimFixture f;
  auto out = RunCapture(
      "class V #(int size = 1);\n"
      "  function int w(); return size; endfunction\n"
      "endclass\n"
      "class Holder;\n"
      "  typedef V#(4) v4;\n"
      "  typedef V#(8) v8;\n"
      "  function int a(); v4 x = new; return x.w(); endfunction\n"
      "  function int b(); v8 y = new; return y.w(); endfunction\n"
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

// §8.25 (printed page 204 of IEEE 1800-2023): a type parameter used in a type
// resolves to a type only after elaboration, so a class-scope typedef whose
// actuals name the class's own parameter -- UVM's `typedef
// uvm_object_registry#(T,Tname) this_type;` -- names a different
// specialization in each specialization of the class holding it, and cannot be
// settled once for the declaration. Two specializations of the outer class
// discriminate: binding the typedef once, with T standing for nothing, leaves
// both reads at whatever that one inner type gives, and resolving it per
// specialization leaves byte's 8 and shortint's 16.
TEST(ClassSim, ClassScopeTypedefOfTheClassesOwnParameterIsPerSpecialization) {
  SimFixture f;
  auto out = RunCapture(
      "class Box #(type T = int);\n"
      "  function int w(); return $bits(T); endfunction\n"
      "endclass\n"
      "class Reg #(type T = int);\n"
      "  typedef Box#(T) box_t;\n"
      "  function int w(); box_t b = new; return b.w(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  Reg #(byte) rb = new;\n"
      "  Reg #(shortint) rs = new;\n"
      "  initial begin\n"
      "    $display(\"b %0d\", rb.w());\n"
      "    $display(\"s %0d\", rs.w());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "b 8\ns 16\n");
}

// §8.25 (printed page 204 of IEEE 1800-2023) with §6.22.1: two sets of
// parameters are the same only where each type parameter's two types match,
// and `bit [2:0]` and `bit [7:0]` do not, being packed arrays of different
// sizes. W#(bit [2:0]) and W#(bit [7:0]) are therefore two specializations
// with an n each. The keyword the two actuals share is the whole of the name
// the parser records for either, so spelled by that name they are one
// specialization, and both reads give the 8 written last; spelled by the
// keyword and the width, they give 3 and 8.
TEST(ClassSim, BuiltinTypeActualsOfDifferentWidthsAreTwoSpecializations) {
  SimFixture f;
  auto out = RunCapture(
      "class W #(type T = int);\n"
      "  static int n;\n"
      "  function void set(int v); n = v; endfunction\n"
      "  function int get(); return n; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  W #(bit [2:0]) w3 = new;\n"
      "  W #(bit [7:0]) w8 = new;\n"
      "  initial begin\n"
      "    w3.set(3);\n"
      "    w8.set(8);\n"
      "    $display(\"w3 %0d\", w3.get());\n"
      "    $display(\"w8 %0d\", w8.get());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "w3 3\nw8 8\n");
}

// §8.25 (printed page 204 of IEEE 1800-2023): each specialization is a type of
// its own, with its own set of static member variables, and the clause calls
// this consistent with C++ templated classes, where a static variable local
// to a member function has one copy per instantiation. With §6.21's static
// local that is a copy per specialization: UVM's uvm_object_registry#(T)::get
// keeps its singleton in `static this_type m_inst`. Two calls through P#(1)
// and one through P#(2) discriminate: one copy for every specialization reads
// 3 for P#(2), and a copy each reads 1.
TEST(ClassSim, StaticLocalOfAMethodIsPerSpecialization) {
  SimFixture f;
  auto out = RunCapture(
      "class P #(int K = 0);\n"
      "  static function int bump(); static int n; n++; return n;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    void'(P#(1)::bump());\n"
      "    void'(P#(1)::bump());\n"
      "    $display(\"p2 %0d\", P#(2)::bump());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "p2 1\n");
}

// §8.25 with §8.23: a type parameter stands for the type its actual gives, so
// `T::get()` inside H #(type T) calls the static method of the class the
// running specialization binds T to -- UVM's `Tregistry::get()` in
// uvm_registry_common. R and S answer different values, so H#(R) and H#(S)
// each show which class their T reached; a prefix no class is registered
// under resolved to no call at all.
TEST(ClassSim, ScopePrefixNamingATypeParameterNamesItsActualsClass) {
  SimFixture f;
  auto out = RunCapture(
      "class R; static function int get(); return 7; endfunction endclass\n"
      "class S; static function int get(); return 9; endfunction endclass\n"
      "class H #(type T = int);\n"
      "  static function int call(); return T::get(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial $display(\"%0d %0d\", H#(R)::call(), H#(S)::call());\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 9\n");
}

// §8.25 with §8.3: a class-scope typedef is an item of the class declaring it,
// so `this_type` in Reg's `typedef Common #(this_type) common_type;` is Reg's
// own specialization, not the `this_type` Common declares -- UVM's
// uvm_object_registry#(T) handing itself to uvm_registry_common as its
// Tregistry. Common's R::id() then reaches Reg#(A) and Reg#(B), whose T::v()
// answer 3 and 5; read in Common's scope, R named Common, which has no id().
TEST(ClassSim, TypedefNamedInAnActualListIsTheHoldersTypedef) {
  SimFixture f;
  auto out = RunCapture(
      "typedef class Common;\n"
      "class A; static function int v(); return 3; endfunction endclass\n"
      "class B; static function int v(); return 5; endfunction endclass\n"
      "class Reg #(type T = int);\n"
      "  typedef Reg #(T) this_type;\n"
      "  typedef Common #(this_type) common_type;\n"
      "  static function int id(); return T::v(); endfunction\n"
      "  static function int via(); return common_type::call(); endfunction\n"
      "endclass\n"
      "class Common #(type R = int);\n"
      "  typedef Common #(R) this_type;\n"
      "  static function int call(); return R::id(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial $display(\"%0d %0d\", Reg#(A)::via(), Reg#(B)::via());\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 5\n");
}

// §8.25: a type parameter stands for the type its specialization's actual
// gives, so a local `T obj` declared in a method of R#(A) is a handle of A,
// and `new` on it constructs an A whichever form writes it. A reads 3, the
// default Base 1, and a local whose class nobody resolved stays null, -1.
TEST(ClassSim, LocalTypedByATypeParameterIsAHandleOfItsActual) {
  SimFixture f;
  auto out = RunCapture(
      "class Base; virtual function int ident(); return 1; endfunction\n"
      "endclass\n"
      "class A extends Base; function int ident(); return 3; endfunction\n"
      "endclass\n"
      "class R #(type T = Base);\n"
      "  function Base assigned(); T obj; obj = new(); return obj;\n"
      "  endfunction\n"
      "  function Base initialized(); T obj = new(); return obj; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  function int id(Base b); return b == null ? -1 : b.ident();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    R #(A) r = new;\n"
      "    $display(\"%0d %0d\", id(r.assigned()), id(r.initialized()));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 3\n");
}

// §8.25 with §8.20: a method of R#(A) reads A for T however the call reaches
// it. Through a handle of R's abstract base the call carries no list of its
// own, and the object `R #(A) r = new;` built holds the actual; read from
// the default instead, `obj = new();` tried to construct the abstract Base.
TEST(ClassSim, TypeParameterReadThroughAHandleOfTheBaseIsTheObjectsActual) {
  SimFixture f;
  auto out = RunCapture(
      "virtual class Base; pure virtual function int ident(); endclass\n"
      "class A extends Base; function int ident(); return 3; endfunction\n"
      "endclass\n"
      "virtual class W; pure virtual function Base make(); endclass\n"
      "class R #(type T = Base) extends W;\n"
      "  function Base make(); T obj; obj = new(); return obj; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    R #(A) r = new;\n"
      "    W w = r;\n"
      "    Base b = w.make();\n"
      "    $display(\"%0d\", b == null ? -1 : b.ident());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3\n");
}

}  // namespace
