#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.18 (printed page 118) with §8.3 (printed 180): a typedef is a class item
// and a name it declares stands for the type throughout the class, so
// `typedef C this_type;` makes `this_type` a variable's class type as the
// spelling `C` is, and `m_inst = new` on the static declared by it
// constructs. This is uvm_callbacks#(T,CB)'s `local static this_type
// m_inst; ... m_inst = new;`. get() constructs once and returns the one
// object, whose k reads 2 both times, 22. The run bound a typedef of a
// package, a module or the unit to its class and none of a class's own, so
// `this_type` named no class, `new` evaluated to a null handle, and get()
// returned null, 77.
TEST(ClassScopeTypedefSim, StaticDeclaredByAClassScopeTypedefConstructs) {
  EXPECT_EQ(
      RunAndGet(
          "class C;\n"
          "  typedef C this_type;\n"
          "  local static this_type m_inst;\n"
          "  int k = 2;\n"
          "  static function this_type get();\n"
          "    if (m_inst == null) m_inst = new;\n"
          "    return m_inst;\n"
          "  endfunction\n"
          "endclass\n"
          "module t;\n"
          "  int result;\n"
          "  initial begin\n"
          "    C a = C::get();\n"
          "    C b = C::get();\n"
          "    result = (a == null ? 7 : a.k) * 10 + (b == null ? 7 : b.k);\n"
          "  end\n"
          "endmodule\n",
          "result"),
      22u);
}

// §6.18 with §8.13 (printed pages 189-190): a subclass inherits the base's
// members, its typedefs among them, so a local of D's method declared with
// the `super_type` its base C declares is a C, and its `new` constructs one
// whose k reads 5. Looked up in D alone, the name named no class and the
// local stayed null, 7.
TEST(ClassScopeTypedefSim, LocalDeclaredByABaseClassTypedefConstructs) {
  EXPECT_EQ(RunAndGet("class B;\n"
                      "  int k = 5;\n"
                      "endclass\n"
                      "class C extends B;\n"
                      "  typedef B super_type;\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  function int make();\n"
                      "    super_type s;\n"
                      "    s = new;\n"
                      "    return s == null ? 7 : s.k;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D d = new;\n"
                      "    result = d.make();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5u);
}

// §6.18 with §8.3 (printed page 180) and §7.8: a property declared through a
// class's typedef of an associative array is that array -- uvm_phase's
// `protected edges_t m_successors;` under `typedef bit edges_t[uvm_phase];`
// -- and so is one a subclass declares through the base's typedef (§8.13).
// p links q once, D keys q and itself, and p's string-keyed count holds 4:
// 110 + 4000 + 2. Read off the property's own declaration, which writes no
// dimension, each was no array and every write was dropped.
TEST(ClassScopeTypedefSim, PropertyDeclaredByAnAssociativeArrayTypedef) {
  EXPECT_EQ(RunAndGet("class P;\n"
                      "  typedef bit edges_t[P];\n"
                      "  typedef int count_t[string];\n"
                      "  protected edges_t succ;\n"
                      "  count_t counts;\n"
                      "  function void link(P e);\n"
                      "    succ[e] = 1;\n"
                      "    counts[\"a\"] = 4;\n"
                      "  endfunction\n"
                      "  function int n(P e);\n"
                      "    return succ.num() * 100 + succ.exists(e) * 10;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class D extends P;\n"
                      "  edges_t more;\n"
                      "  function int m(P e);\n"
                      "    more[e] = 1;\n"
                      "    more[this] = 1;\n"
                      "    return more.num();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    P p = new;\n"
                      "    P q = new;\n"
                      "    D d = new;\n"
                      "    p.link(q);\n"
                      "    result = p.n(q) + p.counts[\"a\"] * 1000 + d.m(q);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            4112u);
}

// §6.18 with §7.4.4 and §8.3: a local of a method declared by a class-scope
// typedef is an object of the type the typedef stands for, its associative
// dimension included, whether named bare in the declaring class's function
// or through the class scope in another class's task. N's link fills its
// bare-typed local with two keys, 2; H's task fills a `N::edges_t` local
// through a ref formal of the same type and sums the keys' ids, 2 + 3.
// Declared as scalars, neither local held a key: the counts read 0 and the
// foreach ran once with a null key.
TEST(ClassScopeTypedefSim, MethodLocalDeclaredByAnAssociativeArrayTypedef) {
  EXPECT_EQ(RunAndGet("class N;\n"
                      "  int id;\n"
                      "  typedef bit edges_t[N];\n"
                      "  protected edges_t succ;\n"
                      "  function new(int i); id = i; endfunction\n"
                      "  function void add(N n); succ[n] = 1; endfunction\n"
                      "  function void get_succ(ref edges_t out);\n"
                      "    foreach (succ[p]) out[p] = 1;\n"
                      "  endfunction\n"
                      "  function int link(N a, N b);\n"
                      "    edges_t e;\n"
                      "    e[a] = 1; e[b] = 1;\n"
                      "    return e.num();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class H;\n"
                      "  int sum;\n"
                      "  task sync(N n);\n"
                      "    N::edges_t edges;\n"
                      "    n.get_succ(edges);\n"
                      "    foreach (edges[p]) sum += p.id;\n"
                      "  endtask\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    N a = new(1), b = new(2), c = new(3);\n"
                      "    H h = new;\n"
                      "    a.add(b); a.add(c);\n"
                      "    h.sync(a);\n"
                      "    result = a.link(b, c) * 100 + h.sum;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            205u);
}

}  // namespace
