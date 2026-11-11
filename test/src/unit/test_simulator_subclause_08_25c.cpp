#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

namespace {

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

TEST(ClassSim, TypedefNamedMemberOfClassTypedefStacksItsDimensions) {
  SimFixture f;
  auto out = RunCapture(
      "typedef logic [3:0] nib_t;\n"
      "class Box #(int W = 2);\n"
      "  typedef struct packed { nib_t [W-1:0] x; logic y; } S;\n"
      "  S s;\n"
      "  function void show();\n"
      "    s = 9'h1A5;\n"
      "    $display(\"%0d %0d %0d\", $bits(s), s.x, s.y);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  Box #() b;\n"
      "  initial begin\n"
      "    b = new;\n"
      "    b.show();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "9 210 1\n");
}

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

TEST(ParameterizedClassSim, PortParameterArrayHoldsItsElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C #(parameter int A[2] = '{1, 2});\n"
                       "  static function int second(); return A[1]; "
                       "endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial $display(\"%0d %0d\", C#()::A[0], "
                       "C#()::second());\n"
                       "endmodule\n",
                       f),
            "1 2\n");
}

TEST(ParameterizedClassSim, PortParameterArrayTakesTheActual) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C #(parameter int A[2] = '{1, 2}, int W = 3);\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial $display(\"%0d %0d\", C#('{5, 6})::A[1], "
                       "C#(.W(4))::A[1]);\n"
                       "endmodule\n",
                       f),
            "6 2\n");
}

TEST(ClassSim, AModulesGenericClassIsEachInstancesOwn) {
  const std::string kSrc =
      "package p;\n"
      "  class P #(int N = 1);\n"
      "    static int count = 0;\n"
      "    function new(); count++; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module sub;\n"
      "  import p::*;\n"
      "  class C #(int N = 1);\n"
      "    static int count = 0;\n"
      "    function new(); count++; endfunction\n"
      "  endclass\n"
      "  C #(4) a, b;\n"
      "  C c;\n"
      "  P #(4) x;\n"
      "  p::P #(4) y;\n"
      "  int n, d, m, mp;\n"
      "  initial begin\n"
      "    a = new; b = new; c = new; x = new; y = new;\n"
      "    #1 n = C#(4)::count; d = C#()::count; m = P#(4)::count;\n"
      "    mp = p::P#(4)::count;\n"
      "  end\n"
      "endmodule\n"
      "module t; sub u1(); sub u2(); endmodule\n";
  for (const std::string kInst : {"u1", "u2"}) {
    EXPECT_EQ(RunAndGet(kSrc, (kInst + ".n").c_str()), 2u) << kInst;
    EXPECT_EQ(RunAndGet(kSrc, (kInst + ".d").c_str()), 1u) << kInst;
    EXPECT_EQ(RunAndGet(kSrc, (kInst + ".m").c_str()), 4u) << kInst;
    EXPECT_EQ(RunAndGet(kSrc, (kInst + ".mp").c_str()), 4u) << kInst;
  }
}

TEST(ClassSim, AClassNestedInAnInstancesGenericClassIsItsOwn) {
  const std::string kSrc =
      "module sub;\n"
      "  class O #(int N = 1);\n"
      "    class K;\n"
      "      static int count = 0;\n"
      "      function new(); count++; endfunction\n"
      "    endclass\n"
      "    class I #(int M = 1);\n"
      "      static int count = 0;\n"
      "      function new(); count++; endfunction\n"
      "    endclass\n"
      "    static function int make();\n"
      "      K k = new;\n"
      "      return K::count;\n"
      "    endfunction\n"
      "    static function int make2();\n"
      "      I #(2) j = new;\n"
      "      return I#(2)::count;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int n, s;\n"
      "  initial #1 begin n = O#()::make(); s = O#()::make2(); end\n"
      "endmodule\n"
      "module t; sub u1(); sub u2(); endmodule\n";
  for (const std::string kInst : {"u1", "u2"}) {
    EXPECT_EQ(RunAndGet(kSrc, (kInst + ".n").c_str()), 1u) << kInst;
    EXPECT_EQ(RunAndGet(kSrc, (kInst + ".s").c_str()), 1u) << kInst;
  }
}

TEST(ClassSpecializationSim, ProcessNamedSpecializationStaticsAreSetEarly) {
  const char* src =
      "int g = 1;\n"
      "class C #(int N = 0);\n"
      "  static int s = $unit::g + N;\n"
      "  static function int f(); static int l = $unit::g * 10 + N;\n"
      "    return l;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r, u;\n"
      "  initial begin $unit::g = 2; r = C#(3)::s; u = C#(4)::f(); end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 4u);
  EXPECT_EQ(RunAndGet(src, "u"), 14u);
}

TEST(ClassSpecializationSim, SubroutineNamedSpecializationStaticsAreSetEarly) {
  const char* src =
      "int g = 1;\n"
      "class C #(int N = 0); static int s = $unit::g + N; endclass\n"
      "class D; static function int f(); return C#(5)::s; endfunction\n"
      "endclass\n"
      "class E #(int K = 0);\n"
      "  static function int f(); return C#(K)::s; endfunction\n"
      "endclass\n"
      "typedef E#(30) e30;\n"
      "function int uf(); return C#(6)::s; endfunction\n"
      "module t;\n"
      "  int r, u, v, w;\n"
      "  function int mf(); return C#(7)::s; endfunction\n"
      "  initial begin\n"
      "    $unit::g = 2; r = D::f(); u = uf(); v = mf(); w = e30::f();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 6u);
  EXPECT_EQ(RunAndGet(src, "u"), 7u);
  EXPECT_EQ(RunAndGet(src, "v"), 8u);
  EXPECT_EQ(RunAndGet(src, "w"), 31u);
}

TEST(ClassSpecializationSim, DeclaredAndInstanceSpecializationsAreSetEarly) {
  const char* src =
      "int g = 1;\n"
      "class C #(int N = 0); static int s = $unit::g + N; endclass\n"
      "module m #(parameter int P = 0);\n"
      "  int r;\n"
      "  initial begin $unit::g = 2; r = C#(P)::s; end\n"
      "endmodule\n"
      "module t;\n"
      "  m #(20) a();\n"
      "  int r, v;\n"
      "  initial begin\n"
      "    $unit::g = 2;\n"
      "    begin C#(8) h; h = new; r = h.s; end\n"
      "    #1 v = a.r;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 9u);
  EXPECT_EQ(RunAndGet(src, "v"), 21u);
}

TEST(ClassSpecializationSim, ModuleClassMethodSpecializationsAreSetEarly) {
  const char* src =
      "int g = 1;\n"
      "class C #(int N = 0); static int s = $unit::g + N; endclass\n"
      "module m #(parameter int P = 0);\n"
      "  class E; static function int f(); return C#(P)::s; endfunction\n"
      "  endclass\n"
      "  int r;\n"
      "  initial begin $unit::g = 2; r = E::f(); end\n"
      "endmodule\n"
      "module t;\n"
      "  m #(20) a();\n"
      "  m #(30) b();\n"
      "  int r, v;\n"
      "  initial #1 begin r = a.r; v = b.r; end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 21u);
  EXPECT_EQ(RunAndGet(src, "v"), 31u);
}

TEST(ClassSpecializationSim, OverriddenDefaultsReshapeRangesAndDimensions) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class Grid #(type T = byte, int size = 3);\n"
                 "  T up[0:size-1];\n"
                 "  T down[size+1:2];\n"
                 "  T grid[size][2];\n"
                 "endclass\n"
                 "module t;\n"
                 "  Grid#(shortint, 6) g;\n"
                 "  Grid d;\n"
                 "  initial begin\n"
                 "    g = new;\n"
                 "    d = new;\n"
                 "    g.up[5] = 16'h0AAA;\n"
                 "    g.down[7] = 16'h0BBB;\n"
                 "    g.grid[5][1] = 16'h0CCC;\n"
                 "    d.grid[2][1] = 8'h5A;\n"
                 "    $display(\"%0d %0d %0d %h\", $size(g.up), $left(g.up), "
                 "$right(g.up), g.up[5]);\n"
                 "    $display(\"%0d %0d %0d %h\", $size(g.down), "
                 "$right(g.down), $left(g.down), g.down[7]);\n"
                 "    $display(\"%0d %0d %h\", $size(g.grid), "
                 "$size(g.grid, 2), g.grid[5][1]);\n"
                 "    $display(\"%0d %0d %0d %0d %h\", $size(d.up), "
                 "$left(d.down), $size(d.grid), $size(d.grid, 2), "
                 "d.grid[2][1]);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "6 0 5 0aaa\n6 2 7 0bbb\n6 2 0ccc\n3 4 3 2 5a\n");
  EXPECT_FALSE(f.has_errors);
}

const char* const kHeaderDefaultNamingAnEarlierParameterSrc =
    "class C #(parameter int A = 3, parameter int B = A * 2);\n"
    "  localparam int N = A + 1;\n"
    "endclass\n"
    "class D #(parameter logic [3:0] L = 4'b1x1x,\n"
    "          parameter bit [3:0] W = L,\n"
    "          parameter logic [3:0] M = L);\n"
    "endclass\n"
    "class RC #(parameter real X = 1.5, parameter real Y = X * 2);\n"
    "endclass\n"
    "module top;\n"
    "  int r1, r2, r3, r4, r5, r6;\n"
    "  logic [3:0] w1, w2, m1, m2;\n"
    "  real y1, y2;\n"
    "  initial begin\n"
    "    r1 = C#(5)::B;\n"
    "    r2 = C#()::B;\n"
    "    r3 = C#(.A(5))::B;\n"
    "    r4 = C#(5)::N;\n"
    "    w1 = D#(4'bz1z1)::W;\n"
    "    w2 = D#()::W;\n"
    "    m1 = D#(4'bz1z1)::M;\n"
    "    m2 = D#()::M;\n"
    "    y1 = RC#(2.5)::Y;\n"
    "    y2 = RC#()::Y;\n"
    "    r5 = (m1 === 4'bz1z1) && (m2 === 4'b1x1x);\n"
    "    r6 = (y1 == 5.0) * 10 + (y2 == 3.0);\n"
    "  end\n"
    "endmodule\n";

TEST(ClassSim, BodyParameterOfASpecializationReadsItsHeaderValue) {
  SimFixture f;
  auto* design = ElaborateSrc(kHeaderDefaultNamingAnEarlierParameterSrc, f);
  LowerRunAndCheck(f, design, {{"r4", 6u}});
}

TEST(ClassSim, DISABLED_HeaderDefaultNamingAnEarlierParameterReadsItsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(kHeaderDefaultNamingAnEarlierParameterSrc, f);
  LowerRunAndCheck(f, design,
                   {{"r1", 10u},
                    {"r2", 6u},
                    {"r3", 10u},
                    {"w1", 5u},
                    {"w2", 10u},
                    {"r5", 1u},
                    {"r6", 11u}});
}

TEST(ClassSim, SpecializationTypedefOfAnIntegralActualHasItsWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class PC #(type T = int); typedef T X; endclass\n"
      "module top;\n"
      "  PC#(byte)::X v2;\n"
      "  int r1;\n"
      "  initial r1 = $bits(v2);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 8u}});
}

TEST(ClassSim, DISABLED_SpecializationTypedefKeepsTheActualsDimensions) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "typedef int UQ[$];\n"
      "typedef byte UA[3];\n"
      "class PC #(type T = int); typedef T X; endclass\n"
      "package pk;\n"
      "  typedef int PQ[$];\n"
      "  class KC #(type T = int); typedef T X; endclass\n"
      "  PC#(UQ)::X pv;\n"
      "endpackage\n"
      "PC#(UQ)::X uv;\n"
      "interface ifc;\n"
      "  PC#(UQ)::X iv;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc ii();\n"
      "  PC#(UQ)::X v1;\n"
      "  PC#(byte)::X v2;\n"
      "  PC#(UA)::X v3;\n"
      "  typedef PC#(UQ)::X TQ;\n"
      "  TQ v4;\n"
      "  PC#(.T(UQ))::X v6;\n"
      "  pk::KC#(pk::PQ)::X v7;\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12;\n"
      "  initial begin\n"
      "    PC#(UQ)::X v5;\n"
      "    v1.push_back(1); r1 = v1.size();\n"
      "    v4.push_back(1); r2 = v4.size();\n"
      "    v5.push_back(1); r3 = v5.size();\n"
      "    pk::pv.push_back(1); r4 = pk::pv.size();\n"
      "    uv.push_back(1); r5 = uv.size();\n"
      "    ii.iv.push_back(1); r6 = ii.iv.size();\n"
      "    r7 = $size(v3);\n"
      "    r8 = $bits(PC#(byte)::X);\n"
      "    r9 = $bits(v2);\n"
      "    v6.push_back(1); r10 = v6.size();\n"
      "    v7.push_back(1); r11 = v7.size();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 1u},
                    {"r2", 1u},
                    {"r3", 1u},
                    {"r4", 1u},
                    {"r5", 1u},
                    {"r6", 1u},
                    {"r7", 3u},
                    {"r8", 8u},
                    {"r9", 8u},
                    {"r10", 1u},
                    {"r11", 1u}});
}

}  // namespace
