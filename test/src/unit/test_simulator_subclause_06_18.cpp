#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/block_enums.h"
#include "simulator/sim_context.h"

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

// §6.18 with A.2.8: a block's typedef of a type that is no enumeration,
// structure or union names that type for the declarations after it, so `T x`
// is a 4-state `logic [7:0]` that starts at x and keeps eight bits of 9'h1FF,
// `I i` a signed int and `R r` a real. §7.4.4 stacks a packed dimension
// written where the name is used outside the type's own: `T [1:0] w` keeps
// sixteen bits of 17'h1ABCD, and `B1 [3:0] v` four bits of 5'h1F. A function
// body's `N n` keeps four bits of 5'h1F too. A4, whose unpacked dimension a
// declaration would adopt, names no plain type and declares nothing here.
// Each fell to the 32-bit carrier of a type nothing sizes, the real included.
TEST(TypedefSim, BlockTypedefOfAPlainTypeNamesALaterDeclarationsType) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  function automatic int f();\n"
                 "    typedef bit [3:0] N;\n"
                 "    N n;\n"
                 "    n = 5'h1F;\n"
                 "    return n;\n"
                 "  endfunction\n"
                 "  initial begin\n"
                 "    typedef logic [7:0] T;\n"
                 "    typedef int I;\n"
                 "    typedef real R;\n"
                 "    typedef bit B1;\n"
                 "    typedef int A4 [4];\n"
                 "    T x;\n"
                 "    I i;\n"
                 "    R r;\n"
                 "    T [1:0] w;\n"
                 "    B1 [3:0] v;\n"
                 "    $display(\"%b\", x);\n"
                 "    x = 9'h1FF;\n"
                 "    i = -1;\n"
                 "    r = 1.5;\n"
                 "    w = 17'h1ABCD;\n"
                 "    v = 5'h1F;\n"
                 "    $display(\"%0d %0d %0d %f %0d %h %0d %0d\", $bits(x),"
                 " x, i, r, $bits(w), w, v, f());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "xxxxxxxx\n8 255 -1 1.500000 16 abcd 15 15\n");
}

// §6.18 with §7.4.4: a block typedef whose type is another of the block's
// type names stands for whatever that one does. `T2 z` is T's eight bits,
// `T3 y` sixteen with T3's `[1:0]` stacked outside them, `E2 e` the block's
// enumeration, whose name() answers K, and the type parameter `P q`, given
// T2, eight bits again. A typedef of a package's type, `PT u`, is that
// type's three bits. Each name through a block name stood for only the bare
// name, which no table sizes.
TEST(TypedefSim, BlockTypedefOfAnotherBlockTypeNameStandsForWhatThatOneDoes) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p;\n"
                 "  typedef logic [2:0] pt;\n"
                 "endpackage\n"
                 "module t;\n"
                 "  initial begin\n"
                 "    typedef logic [7:0] T;\n"
                 "    typedef T T2;\n"
                 "    typedef T [1:0] T3;\n"
                 "    typedef enum {A, B, K} E;\n"
                 "    typedef E E2;\n"
                 "    typedef p::pt PT;\n"
                 "    parameter type P = T2;\n"
                 "    T2 z;\n"
                 "    T3 y;\n"
                 "    E2 e;\n"
                 "    PT u;\n"
                 "    P q;\n"
                 "    z = 10'h3FE;\n"
                 "    y = 17'h1ABCD;\n"
                 "    e = K;\n"
                 "    u = 4'hF;\n"
                 "    q = 9'h1FF;\n"
                 "    $display(\"%0d %0d %0d %h %s %0d %0d %0d\", $bits(z), z,"
                 " $bits(y), y, e.name(), $bits(u), u, q);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "8 254 16 abcd K 3 7 255\n");
}

// §6.18 with §7.4: a declaration writing unpacked dimensions after a block
// typedef's name is an array of the typedef's type, so each element of
// `T a [2]` is a `logic [7:0]` keeping eight bits of 9'h1FF, in a begin-end
// block and a function body alike. The elements took nothing from the name
// and fell to the 32-bit carrier.
TEST(TypedefSim, ArrayOfABlockTypedefHasElementsOfItsType) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  function automatic int f();\n"
                 "    typedef bit [3:0] N;\n"
                 "    N n [3];\n"
                 "    n[2] = 5'h1F;\n"
                 "    return n[2];\n"
                 "  endfunction\n"
                 "  initial begin\n"
                 "    typedef logic [7:0] T;\n"
                 "    T a [2];\n"
                 "    a[1] = 9'h1FF;\n"
                 "    $display(\"%0d %0d %0d\", $bits(a[1]), a[1], f());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "8 255 15\n");
}

// The walk RegisterBlockEnumTypes makes over a subroutine body steps over a
// null statement and goes on to the items after it, so a typedef following
// one still reshapes the declaration by its name to the type it stands for,
// here int. Parser::ParseSubroutineBody keeps whatever Parser::ParseStmt
// answers, null included, and no source text the unit tests parse has it
// answer null, so the body is built here. The module is walked with no
// design, which leaves the compilation unit's constants and classes out.
TEST(TypedefSim, BlockTypeNameWalkStepsOverANullStatement) {
  SimFixture f;
  auto* td = f.arena.Create<ModuleItem>();
  td->kind = ModuleItemKind::kTypedef;
  td->name = "T";
  td->typedef_type.kind = DataTypeKind::kInt;
  auto* td_stmt = f.arena.Create<Stmt>();
  td_stmt->kind = StmtKind::kBlockItemDecl;
  td_stmt->decl_item = td;
  auto* decl = f.arena.Create<Stmt>();
  decl->kind = StmtKind::kVarDecl;
  decl->var_decl_type.kind = DataTypeKind::kNamed;
  decl->var_decl_type.type_name = "T";
  decl->var_name = "x";
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->func_body_stmts = {nullptr, td_stmt, decl};
  RtlirModule mod;
  mod.function_decls.push_back(func);
  RegisterBlockEnumTypes(&mod, nullptr, f.ctx, f.arena);
  auto& shaped_decls = f.ctx.ClassTypedefShapedDecls();
  ASSERT_TRUE(shaped_decls.contains(decl));
  EXPECT_EQ(shaped_decls.at(decl)->var_decl_type.kind, DataTypeKind::kInt);
}

}  // namespace
