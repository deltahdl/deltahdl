#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

// §8.25 (printed pages 203-204 of IEEE 1800-2023): a specialization's methods
// run under that specialization, and an initializer that constructs one builds
// it rather than the generic class. Split out of
// test_simulator_subclause_08_25b.cpp, whose opening comment gives the reason
// these cases run the whole pipeline on source text.

namespace {

// §8.25 with §8.20: a virtual method called on an object of Own #(byte) is
// Own #(byte)'s method, so `rsrc_t`, Own's `typedef R #(T) rsrc_t;`, names
// R #(byte) in it as in the non-virtual one, and both read R #(byte)'s 9. The
// specialization's vtable, copied from the declaration, named the generic Own
// as the virtual method's class, which the call ran under: rsrc_t resolved
// there, to another R, and read 0 -- UVM's resource pool compared the type
// handle `rsrc_t::get_type()` its default implementation's virtual
// get_by_name passed against each resource's own and matched none.
TEST(ClassSim, VirtualMethodOfASpecializationRunsUnderTheSpecialization) {
  SimFixture f;
  auto out = RunCapture(
      "class R #(type T = int);\n"
      "  static int id;\n"
      "endclass\n"
      "class Own #(type T = int);\n"
      "  typedef R #(T) rsrc_t;\n"
      "  virtual function int get_v(); return rsrc_t::id; endfunction\n"
      "  function int get_nv(); return rsrc_t::id; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static Own #(byte) o = new;\n"
      "    R#(int)::id = 7;\n"
      "    R#(byte)::id = 9;\n"
      "    $display(\"%0d %0d\", o.get_v(), o.get_nv());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "9 9\n");
}

// The same where the virtual method overrides a base's pure virtual one and
// the typedef is the base's, as uvm_resource_db_default_implementation_t
// #(T) implements uvm_resource_db_implementation_t #(T)'s get_by_name with
// the base's rsrc_t: the override runs as Imp #(byte)'s, whose base is
// ImpBase #(byte), so the inherited rsrc_t is R #(byte) and reads 9.
TEST(ClassSim, OverrideOfASpecializationReadsItsBasesTypedef) {
  SimFixture f;
  auto out = RunCapture(
      "class R #(type T = int);\n"
      "  static int id;\n"
      "endclass\n"
      "virtual class ImpBase #(type T = int);\n"
      "  typedef R #(T) rsrc_t;\n"
      "  pure virtual function int get();\n"
      "endclass\n"
      "class Imp #(type T = int) extends ImpBase #(T);\n"
      "  virtual function int get(); return rsrc_t::id; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static Imp #(byte) i = new;\n"
      "    ImpBase #(byte) h;\n"
      "    R#(int)::id = 7;\n"
      "    R#(byte)::id = 9;\n"
      "    h = i;\n"
      "    $display(\"%0d %0d\", i.get(), h.get());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "9 9\n");
}

// §8.25 (printed pages 203-204): a declaration's initializer `new`
// constructs the specialization the declared type names, so the constructor
// that runs is S #(byte)'s and increments its static n rather than the
// default specialization's; built as the generic S, the count went to
// S #(int)::n.
TEST(ClassSim, DeclarationInitializerNewBuildsTheSpecialization) {
  SimFixture f;
  auto out = RunCapture(
      "class S #(type T = int);\n"
      "  static int n;\n"
      "  function new(); n++; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static S #(byte) a = new;\n"
      "    $display(\"%0d %0d\", S#(byte)::n, S#(int)::n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0\n");
}

// The same rule for a local declared in a function body, which is declared
// by a path of its own and had recorded no specialization at all.
TEST(ClassSim, FunctionLocalInitializerNewBuildsTheSpecialization) {
  SimFixture f;
  auto out = RunCapture(
      "class S #(type T = int);\n"
      "  static int n;\n"
      "  function new(); n++; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  function automatic void g(); S #(byte) l = new; endfunction\n"
      "  initial begin\n"
      "    g();\n"
      "    $display(\"%0d %0d\", S#(byte)::n, S#(int)::n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0\n");
}

// §6.20.4 with §8.25: a localparam in a parameterized class body is a
// constant of each specialization, so `N = W * 2` is 16 for C#(8) and for
// the default specialization C#() and C, 8 for C#(4), and the same inside a
// method run on an object of each; K, which names no parameter, is 3 in all.
TEST(ClassParamsSim, BodyLocalparamFoldsInEachSpecialization) {
  SimFixture f;
  auto out = RunCapture(
      "class C #(int W = 8);\n"
      "  localparam int N = W * 2;\n"
      "  localparam int K = 3;\n"
      "  function int n(); return N; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C #(4) c4;\n"
      "  C c8;\n"
      "  initial begin\n"
      "    c4 = new;\n"
      "    c8 = new;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", C#(8)::N, C#(4)::N, C#()::N,\n"
      "             c4.n(), c8.n(), C#(4)::K);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "16 8 16 8 16 3\n");
}

// §6.18 with §8.25: a class typedef naming a type parameter names the type the
// specialization binds it to, so in C #(byte) `typedef T U;` is byte: $bits(U)
// in a method is 8, as $bits(T) is, and a property declared U holding 8'hFF
// reads -1, as one declared T does. Sized under the declaration's default,
// $bits(U) was int's 32 and the property 255.
TEST(ClassParamsSim, TypedefOfATypeParameterFollowsTheSpecialization) {
  SimFixture f;
  auto out = RunCapture(
      "class C #(type T = int);\n"
      "  typedef T U;\n"
      "  function int b(); return $bits(U); endfunction\n"
      "  U q;\n"
      "endclass\n"
      "module t;\n"
      "  C #(byte) c;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    c.q = 8'hFF;\n"
      "    $display(\"%0d %0d\", c.b(), c.q);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8 -1\n");
}

// §6.20.3 with §8.25: a local type parameter of the class body names its
// default's type in each specialization, so in C #(byte) `localparam type U
// = T;` is byte and $bits(U) in a method is 8, as $bits(T) is.
TEST(ClassParamsSim, BodyLocalTypeParamFollowsTheSpecialization) {
  SimFixture f;
  auto out = RunCapture(
      "class C #(type T = int);\n"
      "  localparam type U = T;\n"
      "  function int b(); return $bits(U); endfunction\n"
      "  function int t(); return $bits(T); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C #(byte) c;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    $display(\"%0d %0d\", c.b(), c.t());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8 8\n");
}

// §8.25 with §7.8: a class variable declared among a module's items with a
// specialization, `Box #(string, 6) bs;`, binds the type parameter to string,
// so its `int m[T]` property is keyed by strings: two keys written through
// the handle stay two entries, each with its own value, while the default
// specialization's `int m[T]` keys by int.
TEST(ClassParamsSim, ModuleLevelSpecializationKeysATypeIndexedProperty) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  class Box #(type T = int, int N = 3);\n"
      "    int m[T];\n"
      "  endclass\n"
      "  Box #(string, 6) bs;\n"
      "  Box bi;\n"
      "  initial begin\n"
      "    bs = new; bi = new;\n"
      "    bs.m[\"k\"] = 77; bs.m[\"kk\"] = 5; bi.m[3] = 9;\n"
      "    $display(\"%0d %0d %0d %0d\", bs.m.num(), bs.m[\"k\"],\n"
      "             bs.m[\"kk\"], bi.m[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 77 5 9\n");
}

// §8.25 with §8.23 and §13.4: a structure typedef a parameterized class
// declares is of the widths each specialization binds, inside its methods as
// well as outside. A function's return variable and a local of the typedef
// have a 32-bit `data` under `B#(32)` and an 8-bit one under the default,
// `p = 8`, so 200 survives under the default, and 300 is cut to 44 there.
TEST(ClassParamsSim, SubroutineVariableOfAParameterizedStructTypedef) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class B #(parameter p = 8);\n"
      "    typedef struct { real r; bit [p-1:0] data; } S;\n"
      "    static function S One(int v); One.data = v; endfunction\n"
      "    static function S Two(); Two.data = 7; Two.r = 1.5; endfunction\n"
      "    static function S Three(); S v; v.data = 300; return v; "
      "endfunction\n"
      "  endclass\n"
      "  B#()::S u, x;\n"
      "  B#(32)::S z, w;\n"
      "  initial begin\n"
      "    u = B#()::One(200); x = B#()::Three();\n"
      "    z = B#(32)::Two(); w = B#(32)::Three();\n"
      "    $display(\"%0d %0d | %0d %f | %0d\", u.data, x.data, z.data, z.r,\n"
      "             w.data);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "200 44 | 7 1.500000 | 300\n");
}

// §8.25 with §20.6.2: a type parameter named through a specialization is the
// type its list binds, shortint for `C#(shortint)::T`, and the default for
// `C#()::T`.
TEST(ClassSim, BitsOfATypeParameterNamedThroughASpecialization) {
  auto v = RunAndGet(
      "class C #(type T = int);\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = $bits(C#(shortint)::T) * 100 + $bits(C#()::T);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1632u);
}

// §8.25: a method local declared with the class's type parameter is of the
// type the running specialization binds, a signed byte under `C #(byte)`, so
// 8'hFF held in it reads -1.
TEST(ClassSim, MethodLocalOfATypeParameterHasTheBoundType) {
  auto v = RunAndGet(
      "class C #(type T = int);\n"
      "  function int w(); T x; x = 8'hFF; return x; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C #(byte) c;\n"
      "  int result;\n"
      "  initial begin c = new; result = c.w() + 2; end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// §8.25: bound to a structure type, the local has the structure's members.
TEST(ClassSim, MethodLocalOfATypeParameterBoundToAStruct) {
  auto v = RunAndGet(
      "typedef struct { byte a; shortint b; } pair_t;\n"
      "class S #(type T = int);\n"
      "  function int m(); T x; x.a = -3; x.b = 300; return x.a + x.b;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  S #(pair_t) s;\n"
      "  int result;\n"
      "  initial begin s = new; result = s.m(); end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 297u);
}

// §8.13 with §8.25: a base named by an extends clause is the specialization
// its list names, positional or named, and an actual naming the derived
// class's own parameter stands for that parameter's value in each
// specialization of the derived class.
TEST(ClassSim, ExtendsClauseValueParametersBindTheBaseLevel) {
  auto v = RunAndGet(
      "class Mem #(real D = 1.5, int K = 1);\n"
      "  function real d(); return D; endfunction\n"
      "  function int k(); return K; endfunction\n"
      "endclass\n"
      "class E extends Mem #(2.25, 4);\n"
      "endclass\n"
      "class G #(int W = 3) extends Mem #(.K(W));\n"
      "endclass\n"
      "module t;\n"
      "  E e; G g; G #(8) g8;\n"
      "  int result;\n"
      "  initial begin\n"
      "    e = new; g = new; g8 = new;\n"
      "    result = (e.d() == 2.25) * 1000 + e.k() * 100 + g.k() * 10 +\n"
      "             g8.k();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1438u);
}

// §8.25 with §8.23: a structure typedef a parameterized class declares has the
// widths its specialization binds, and a property declared by it holds that
// structure, so a method of `Box #(16)` selects its two 16-bit members and
// $bits counts 32, and one of `Box #()` counts 16 under the default W = 8.
// The property had no layout in either and read 0, with $bits 32 in both.
TEST(ClassSim, PropertyOfParameterizedClassTypedefHasSpecializationLayout) {
  SimFixture f;
  auto out = RunCapture(
      "class Box #(int W = 8);\n"
      "  typedef struct { bit [W-1:0] a; bit [W-1:0] b; } S;\n"
      "  S s;\n"
      "  function void set(); s.b = 5; s.a = 3; endfunction\n"
      "  function void show();\n"
      "    $display(\"%0d %0d %0d\", s.a, s.b, $bits(s));\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  Box #(16) b; Box #() d;\n"
      "  initial begin\n"
      "    b = new; b.set(); b.show();\n"
      "    d = new; d.set(); d.show();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 5 32\n3 5 16\n");
}

// §8.13 with §8.23 and §8.25: a class extending a specialization of a
// parameterized base reaches the base's structure typedef bare, with the widths
// that base specialization binds, so Der's `S s` under `Base #(16)` has two
// 16-bit members, and D #(4)'s under the `Base #(N)` it extends has two 4-bit
// ones. The typedef of a base with value parameters was left unresolved, and
// the members read 0 in a 32-bit carrier.
TEST(ClassSim, PropertyOfParameterizedBaseTypedefHasBaseSpecializationLayout) {
  SimFixture f;
  auto out = RunCapture(
      "class Base #(int W = 8);\n"
      "  typedef struct { bit [W-1:0] a; bit [W-1:0] b; } S;\n"
      "endclass\n"
      "class Der extends Base #(16);\n"
      "  S s;\n"
      "  function void show();\n"
      "    s.b = 5; s.a = 3;\n"
      "    $display(\"%0d %0d %0d\", s.a, s.b, $bits(s));\n"
      "  endfunction\n"
      "endclass\n"
      "class D #(int N = 2) extends Base #(N);\n"
      "  S s;\n"
      "  function void show();\n"
      "    s.b = 5; s.a = 3;\n"
      "    $display(\"%0d %0d %0d\", s.a, s.b, $bits(s));\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  Der d; D #(4) e;\n"
      "  initial begin d = new; d.show(); e = new; e.show(); end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 5 32\n3 5 8\n");
}

// §8.25 with §8.9: each specialization has its own copy of a static array
// property, initialized with its own value parameter, and the scope form
// `P#(5)::a` names that copy -- written through it, it reads back through it
// and from the specialization's static method, and not through `P#(9)::`.
// The scope form named the generic class's elements, one storage for every
// specialization, and the static method read a third copy that held 0.
TEST(ParameterizedClassSim, SpecializationStaticArrayIsItsOwn) {
  SimFixture f;
  std::string out = RunCapture(
      "class P #(int N = 2);\n"
      "  static int a[2] = '{N, N + 1};\n"
      "  static int d[];\n"
      "  static function int rd(); return a[0]; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    $display(\"%0d %0d\", P#(5)::a[1], P#(9)::a[0]);\n"
      "    P#(5)::a[0] = 11;\n"
      "    P#(9)::a[0] = 22;\n"
      "    P#(5)::d = new[3];\n"
      "    $display(\"%0d %0d %0d %0d %0d\", P#(5)::a[0], P#(9)::a[0],\n"
      "             P#(5)::rd(), P#(5)::d.size(), P#(9)::d.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "6 9\n11 22 11 3 0\n");
}

// §8.25 with §20.6.2: a property's packed dimension sized by `$bits` of a type
// parameter is as wide as the type the specialization binds it to, eight bits
// for `C #(byte)` and the default's sixteen for `C #()`.
TEST(ParameterizedClassSim, APackedDimensionSizedByATypeParameterFollowsIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C #(type T = logic [15:0]);\n"
                       "  bit [$bits(T)-1:0] mirror;\n"
                       "endclass\n"
                       "module t;\n"
                       "  C #(byte) b = new;\n"
                       "  C #() d = new;\n"
                       "  initial $display(\"%0d %0d\", $bits(b.mirror), "
                       "$bits(d.mirror));\n"
                       "endmodule\n",
                       f),
            "8 16\n");
}

// §6.20.1 with §8.25: a parameter among a class's items declared with an
// unpacked dimension is an array the class holds once, so its elements read
// from its pattern through the class scope and from a static method alike.
TEST(ParameterizedClassSim, BodyParameterArrayHoldsItsElements) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class C;\n"
                 "  parameter int A[2] = '{1, 2};\n"
                 "  static function int second(); return A[1]; "
                 "endfunction\n"
                 "endclass\n"
                 "module t;\n"
                 "  initial $display(\"%0d %0d\", C::A[0], C::second());\n"
                 "endmodule\n",
                 f),
      "1 2\n");
}

// Two unpacked dimensions take a nested pattern, read from an object's method.
TEST(ParameterizedClassSim, BodyParameterArrayOfTwoDimensions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  localparam int M[2][2] = '{'{1, 2}, '{3, 4}};\n"
                       "  function int at(); return M[1][0]; endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  C c = new;\n"
                       "  initial $display(\"%0d\", c.at());\n"
                       "endmodule\n",
                       f),
            "3\n");
}

// Each specialization holds its own elements, filled with its own value
// parameters bound, so P#(5) reads 6 where P#() reads 2.
TEST(ParameterizedClassSim, BodyParameterArrayFollowsTheSpecialization) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class P #(int N = 1);\n"
                       "  localparam int A[2] = '{N, N + 1};\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial $display(\"%0d %0d\", P#(5)::A[1], "
                       "P#()::A[1]);\n"
                       "endmodule\n",
                       f),
            "6 2\n");
}

}  // namespace
