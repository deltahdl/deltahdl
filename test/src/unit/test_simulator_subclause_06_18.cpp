#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
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
          "    static C a = C::get();\n"
          "    static C b = C::get();\n"
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
                      "    static D d = new;\n"
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
                      "    static P p = new;\n"
                      "    static P q = new;\n"
                      "    static D d = new;\n"
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
                      "    static N a = new(1), b = new(2), c = new(3);\n"
                      "    static H h = new;\n"
                      "    a.add(b); a.add(c);\n"
                      "    h.sync(a);\n"
                      "    result = a.link(b, c) * 100 + h.sum;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            205u);
}

// §6.18 makes a typedef name stand for the type it names, so `L x` in a
// procedural block declares a `logic [3:0]`: it starts at x (§6.8, Table 6-7)
// and keeps a z written to it, where §6.11.2 clears x and z only on the way
// into a 2-state type. The `bit` typedef beside it is that 2-state type and
// clears both. The block's variable was made 2-state by the name alone and
// read 0000 and 1001.
TEST(TypedefSim, BlockVariableOfFourStateTypedefKeepsXAndZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef logic [3:0] L;\n"
                       "  typedef bit [3:0] B;\n"
                       "  initial begin : blk\n"
                       "    L x;\n"
                       "    B y;\n"
                       "    $display(\"%b %b\", x, y);\n"
                       "    x = 4'b1z01;\n"
                       "    y = 4'b1z01;\n"
                       "    $display(\"%b %b\", x, y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "xxxx 0000\n1z01 1001\n");
}

// The same rule for a function's locals: §6.18 has `B y` declare the 2-state
// `bit [3:0]` that B names, so it starts at 0 (§6.8, Table 6-7) and clears a
// written z (§6.11.2), and so do an enumeration whose base is `int` (§6.19) and
// a packed structure of `bit` members (§7.2.1) declared by name. The `logic`
// typedef beside them keeps x and z. Every local declared by a name was made
// 4-state and read xxxx, x, xxxx and then 1z01 for B.
TEST(TypedefSim, FunctionLocalOfTwoStateTypedefClearsXAndZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef bit [3:0] B;\n"
                       "  typedef logic [3:0] L;\n"
                       "  typedef enum {P0, P1} E;\n"
                       "  typedef struct packed { bit [1:0] a, b; } S;\n"
                       "  function automatic void f();\n"
                       "    B y; L x; E e; S s;\n"
                       "    $display(\"%b %b %0d %b\", y, x, e, s);\n"
                       "    y = 4'b1z01; x = 4'b1z01;\n"
                       "    $display(\"%b %b\", y, x);\n"
                       "  endfunction\n"
                       "  initial f();\n"
                       "endmodule\n",
                       f),
            "0000 xxxx 0 0000\n1001 1z01\n");
}

// §6.18 with §12.3: a typedef among a procedural block's declarations names
// its type for the declarations after it, so `PP pp` and `UP up` are a packed
// and an unpacked structure whose members keep what is written to them. The
// block's structure typedef stood for no layout, and every member read 0.
TEST(TypedefSim, BlockStructTypedefVariableKeepsMemberWrites) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial begin\n"
                       "    typedef struct packed { logic [7:0] a, b; } PP;\n"
                       "    typedef struct { int a; int b; } UP;\n"
                       "    PP pp;\n"
                       "    UP up;\n"
                       "    pp.a = 3; pp.b = 4; up.a = 5; up.b = 6;\n"
                       "    $display(\"%0d %0d %0d %0d %0d\", pp.a, pp.b,\n"
                       "             up.a, up.b, $bits(pp));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3 4 5 6 16\n");
}

// The same rule in a subroutine: a structure typedef written at the top of a
// function's body, or in a begin-end within it, is the type of the locals
// declared by its name, in a module's function and in a class method alike.
// Each product read 0.
TEST(TypedefSim, SubroutineBlockStructTypedefLocalKeepsMemberWrites) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  function int f();\n"
                       "    typedef struct { int a; int b; } P;\n"
                       "    P p;\n"
                       "    p.a = 3; p.b = 4;\n"
                       "    return p.a * p.b;\n"
                       "  endfunction\n"
                       "  function int g();\n"
                       "    begin\n"
                       "      typedef struct packed { byte a, b; } Q;\n"
                       "      Q q;\n"
                       "      q.a = 5; q.b = 6;\n"
                       "      return q.a * q.b;\n"
                       "    end\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  function automatic int m();\n"
                       "    begin\n"
                       "      typedef struct { int a; int b; } P;\n"
                       "      P p;\n"
                       "      p.a = 7; p.b = 8;\n"
                       "      return p.a * p.b;\n"
                       "    end\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    automatic C c = new;\n"
                       "    $display(\"%0d %0d %0d\", c.f(), c.g(), m());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "12 30 56\n");
}

// §6.18 with §6.19.5: an enumeration a class method's typedef declares is
// the type of the local declared by its name, so name() answers the member
// the local holds. The method's typedef was registered by no walk, and name()
// answered the empty string.
TEST(TypedefSim, MethodEnumTypedefLocalAnswersName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  function string f();\n"
                       "    typedef enum { A, B, K } e_t;\n"
                       "    e_t v;\n"
                       "    v = K;\n"
                       "    return v.name();\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    automatic C c = new;\n"
                       "    $display(\"%s\", c.f());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "K\n");
}

}  // namespace
