#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

namespace {

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
      "    static R #(A) r = new;\n"
      "    $display(\"%0d %0d\", id(r.assigned()), id(r.initialized()));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 3\n");
}

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
      "    static R #(A) r = new;\n"
      "    static W w = r;\n"
      "    static Base b = w.make();\n"
      "    $display(\"%0d\", b == null ? -1 : b.ident());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3\n");
}

TEST(ClassSim, UnitTypedefNamesTheSpecializationItsListSpells) {
  SimFixture f;
  auto out = RunCapture(
      "class V #(int size = 1);\n"
      "  function int w(); return size; endfunction\n"
      "endclass\n"
      "class Base; virtual function int ident(); return 1; endfunction\n"
      "endclass\n"
      "class A extends Base; function int ident(); return 3; endfunction\n"
      "endclass\n"
      "class R #(type T = Base);\n"
      "  function int make(); T obj = new(); return obj.ident(); endfunction\n"
      "endclass\n"
      "typedef V#(6) v6;\n"
      "typedef v6 v6_again;\n"
      "typedef R#(A) ra;\n"
      "module t;\n"
      "  initial begin\n"
      "    static v6 x = new; static v6_again y = new; static ra z = new;\n"
      "    $display(\"%0d %0d %0d\", x.w(), y.w(), z.make());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "6 6 3\n");
}

TEST(ClassSim, ClassScopeTypedefValueActualIsTheHoldersValue) {
  SimFixture f;
  auto out = RunCapture(
      "class Common #(type Tr = int, string Tname = \"<unknown>\");\n"
      "  static function string type_name(); return Tname; endfunction\n"
      "endclass\n"
      "class Reg #(type T = int, string Tname = \"<unknown>\");\n"
      "  typedef Common#(T, Tname) common_type;\n"
      "  static function string name();\n"
      "    return common_type::type_name();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial $display(\"%s %s\", Reg#(int, \"hopper\")::name(),\n"
      "                   Reg#(byte, \"root\")::name());\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hopper root\n");
}

TEST(ClassSim, PropertyTypedByATypeParameterTakesItsActualsQueueDim) {
  SimFixture f;
  auto out = RunCapture(
      "typedef int iq_t[$];\n"
      "class S #(type T = int); T value; endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    S #(iq_t) s;\n"
      "    s = new;\n"
      "    s.value.push_back(7);\n"
      "    s.value.push_back(8);\n"
      "    $display(\"%0d %0d\", s.value.size(), s.value[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 8\n");
}

TEST(ClassSim, PropertyTypedByATypeParameterTakesAHoldersQueueTypedef) {
  SimFixture f;
  auto out = RunCapture(
      "class S #(type T = int); T value; endclass\n"
      "class H;\n"
      "  typedef int iq_t[$];\n"
      "  typedef S #(iq_t) sq_t;\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    H::sq_t s;\n"
      "    s = new;\n"
      "    s.value.push_back(7);\n"
      "    s.value.push_back(8);\n"
      "    $display(\"%0d %0d\", s.value.size(), s.value[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 8\n");
}

TEST(ClassSim, PropertyTypedByATypeParameterTakesAHoldersQueueOfHandles) {
  SimFixture f;
  auto out = RunCapture(
      "class B; int id; function new(int i); id = i; endfunction endclass\n"
      "class S #(type T = int); T value; endclass\n"
      "class H;\n"
      "  typedef B bq_t[$];\n"
      "  typedef S #(bq_t) sq_t;\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    H::sq_t s;\n"
      "    B b;\n"
      "    s = new;\n"
      "    b = new(4);\n"
      "    s.value.push_back(b);\n"
      "    b = new(5);\n"
      "    s.value.push_back(b);\n"
      "    $display(\"%0d\", s.value.size());\n"
      "    if (s.value.size() == 2) $display(\"%0d\", s.value[1].id);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2\n5\n");
}

TEST(ClassSim, SpecializationMadeLateStartsWithItsOwnStatics) {
  SimFixture f;
  auto out = RunCapture(
      "class S #(type T = int);\n"
      "  static int n;\n"
      "  function new(); n++; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static S s = new;\n"
      "    $display(\"%0d\", S#(byte)::n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(ClassSim, ActualsEqualToTheDefaultsNameTheDefaultSpecialization) {
  SimFixture f;
  auto out = RunCapture(
      "class S #(type T = int);\n"
      "  static int n;\n"
      "  function new(); n++; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static S s = new;\n"
      "    $display(\"%0d\", S#(int)::n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

TEST(ClassSim, ScopeFormAssignmentWritesTheSpecializationsStatic) {
  SimFixture f;
  auto out = RunCapture(
      "class S #(type T = int);\n"
      "  static int n = 0;\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    S#(byte)::n = 5;\n"
      "    $display(\"%0d %0d\", S#(byte)::n, S#(int)::n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 0\n");
}

TEST(ClassSim, ScopeFormCompoundAssignmentWritesTheSpecializationsStatic) {
  SimFixture f;
  auto out = RunCapture(
      "class S #(type T = int);\n"
      "  static int n = 1;\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    S#(shortint)::n += 3;\n"
      "    $display(\"%0d %0d\", S#(shortint)::n, S#(int)::n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 1\n");
}

TEST(ClassSim, TypedefActualNamesTheSpecializationOfItsType) {
  SimFixture f;
  auto out = RunCapture(
      "typedef int word_t;\n"
      "class S #(type T = int);\n"
      "  static int n = 0;\n"
      "  function new(); n++; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static S #(int) a = new;\n"
      "    static S #(word_t) b = new;\n"
      "    $display(\"%0d\", S#(int)::n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2\n");
}

TEST(ClassSim, TypedefChainActualNamesTheSpecializationOfItsType) {
  SimFixture f;
  auto out = RunCapture(
      "typedef bit [7:0] u8_t;\n"
      "typedef u8_t u8b_t;\n"
      "class S #(type T = int);\n"
      "  static int n = 0;\n"
      "  function new(); n++; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static S #(bit [7:0]) a = new;\n"
      "    static S #(u8b_t) b = new;\n"
      "    $display(\"%0d %0d\", S#(bit [7:0])::n, S#(int)::n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 0\n");
}

TEST(ClassSim, UnpackedTypedefActualKeepsItsOwnSpecialization) {
  SimFixture f;
  auto out = RunCapture(
      "typedef int iq_t[$];\n"
      "class S #(type T = int);\n"
      "  static int n = 0;\n"
      "  function new(); n++; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static S #(iq_t) a = new;\n"
      "    $display(\"%0d %0d\", S#(iq_t)::n, S#(int)::n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0\n");
}

TEST(ClassSim, TypeParameterPropertyTakesTheActualsWidth) {
  SimFixture f;
  auto out = RunCapture(
      "class S #(type T = int);\n"
      "  T value;\n"
      "  function void put(int v); value = v; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static S #(bit [7:0]) a = new;\n"
      "    static S #(byte) b = new;\n"
      "    static S #(bit [7:0]) c = new;\n"
      "    static S d = new;\n"
      "    a.value = 300;\n"
      "    b.value = 300;\n"
      "    c.put(300);\n"
      "    d.value = 300;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", a.value, b.value, c.value, "
      "d.value,\n"
      "             $bits(a.value));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "44 44 44 300 8\n");
}

TEST(ClassSim, StaticInitializerSizesItsSpecializationsTypeParameter) {
  SimFixture f;
  auto out = RunCapture(
      "class C #(type T = int);\n"
      "  static int w = $bits(T);\n"
      "endclass\n"
      "module t;\n"
      "  initial $display(\"%0d %0d %0d\", C#()::w, C#(int)::w, "
      "C#(byte)::w);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32 8\n");
}

TEST(ClassSim, SpecializationsOfMatchingTypeActualsAreOneType) {
  SimFixture f;
  auto out = RunCapture(
      "class C #(type T = int);\n"
      "  static int n = 0;\n"
      "  function new(); n++; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C #(bit signed [7:0]) a = new;\n"
      "  C #(byte) b = new;\n"
      "  C #(bit [2:0]) c = new;\n"
      "  C #(bit [3:1]) d = new;\n"
      "  C #(logic signed [31:0]) e = new;\n"
      "  C #(integer) g = new;\n"
      "  initial $display(\"%0d %0d %0d %0d\", C#(byte)::n, C#(bit [2:0])::n,\n"
      "                   C#(bit [3:1])::n, C#(integer)::n);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 1 1 2\n");
}

TEST(ClassSim, DeclarationExtendingASpecializationReachesItsStatics) {
  SimFixture f;
  auto out = RunCapture(
      "class C #(type T = bit);\n"
      "  static int tag = 0;\n"
      "  function void add(int v); tag += v; endfunction\n"
      "endclass\n"
      "class D2 #(type P = real) extends C #(integer);\n"
      "  function void bump(); tag = 7; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static D2 d = new;\n"
      "    d.bump();\n"
      "    d.add(2);\n"
      "    $display(\"%0d %0d\", C#()::tag, C#(integer)::tag);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 9\n");
}

TEST(ClassSim, ValueParameterPropertyTakesItsSpecializationsWidth) {
  SimFixture f;
  auto out = RunCapture(
      "class C #(int W = 8);\n"
      "  logic [W-1:0] v;\n"
      "endclass\n"
      "module t;\n"
      "  C #(16) c16;\n"
      "  C #() c8;\n"
      "  initial begin\n"
      "    c16 = new; c16.v = '1;\n"
      "    c8 = new; c8.v = '1;\n"
      "    $display(\"%0d %0d %0d %0d\", c16.v, $bits(c16.v), c8.v,\n"
      "             $bits(c8.v));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "65535 16 255 8\n");
}

}  // namespace
