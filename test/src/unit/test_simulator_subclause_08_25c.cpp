#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

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
      "    Own #(byte) o = new;\n"
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
      "    Imp #(byte) i = new;\n"
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
      "    S #(byte) a = new;\n"
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

}  // namespace
