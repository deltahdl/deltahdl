#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §8.7's own example, with the values the clause says the properties hold once
// an object of D is constructed: c1 is 1, c2 is 2 because the base constructor
// assigns it after the base properties are initialized, d1 is 4, d2 is 2
// because super.new has completed when the derived properties are initialized,
// and d3 is 6. The clause leaves c3 undefined -- D passes d3 to super.new
// before d3 is initialized -- so c3 is left out of the packed result. The
// five values are packed as one integer so that one comparison holds the
// whole example; a derived level initialized before its base constructor ran
// would read d2 as 1.
TEST(ClassConstructorSim, ClauseExamplePropertiesAfterConstruction) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int c1 = 1;\n"
                      "  int c2 = 1;\n"
                      "  int c3 = 1;\n"
                      "  function new(int a);\n"
                      "    c2 = 2;\n"
                      "    c3 = a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  int d1 = 4;\n"
                      "  int d2 = c2;\n"
                      "  int d3 = 6;\n"
                      "  function new;\n"
                      "    super.new(d3);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D obj;\n"
                      "    obj = new;\n"
                      "    result = obj.c1 * 10000 + obj.c2 * 1000 +\n"
                      "             obj.d1 * 100 + obj.d2 * 10 + obj.d3;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            12426u);
}

// §8.7 and §8.15: the derived constructor's first statement, super.new(...),
// is the one call of the base class constructor, made with those arguments.
// The base here takes UVM's uvm_component::new shape, telling the root apart
// by the name and null parent the root's constructor passes and counting every
// construction that took the ordinary path. Running the base constructor once
// with no arguments before the derived body and again from the statement left
// the ordinary count at 1 beside the root flag; the one call with "__top__"
// and null leaves it at 0.
TEST(ClassConstructorSim, LeadingSuperNewIsTheOneBaseConstructorCall) {
  EXPECT_EQ(RunAndGet("class base;\n"
                      "  static int ordinary = 0;\n"
                      "  string nm;\n"
                      "  bit is_root = 0;\n"
                      "  function new(string name, base parent);\n"
                      "    nm = name;\n"
                      "    if (parent == null && name == \"__top__\")\n"
                      "      is_root = 1;\n"
                      "    else\n"
                      "      ordinary = ordinary + 1;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class root extends base;\n"
                      "  function new();\n"
                      "    super.new(\"__top__\", null);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    root r;\n"
                      "    r = new;\n"
                      "    result = r.is_root * 100 + base::ordinary * 10 +\n"
                      "             (r.nm == \"__top__\");\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            101u);
}

// §8.7: the base class constructor is called before the derived class's
// properties are initialized, and the rest of the derived constructor body
// runs after them. A derived property whose default reads what the base
// constructor wrote sees that value, and the derived body then reads the
// initialized property; with the base constructor called from the leading
// super.new after the derived properties were initialized, d would have read
// the base default of 1 and y been 1 instead of 9.
TEST(ClassConstructorSim, DerivedBodyRunsAfterItsPropertiesAreInitialized) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int b = 1;\n"
                      "  function new(int v);\n"
                      "    b = v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int d = b;\n"
                      "  int y;\n"
                      "  function new(int v);\n"
                      "    super.new(v);\n"
                      "    y = d;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived obj;\n"
                      "    obj = new(9);\n"
                      "    result = obj.y * 10 + obj.d;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

// §8.7: an object constructed inside a constructor body is built the same
// way, its own base constructor called once from its leading super.new, while
// the outer construction is under way. The outer derived body constructs an
// inner derived object after its own super.new; the inner base counts its
// constructor runs, and each base run stores the argument it was given.
TEST(ClassConstructorSim, ObjectConstructedInsideAConstructorBodyChainsOnce) {
  EXPECT_EQ(
      RunAndGet("class InnerBase;\n"
                "  static int runs = 0;\n"
                "  int v;\n"
                "  function new(int a);\n"
                "    runs = runs + 1;\n"
                "    v = a;\n"
                "  endfunction\n"
                "endclass\n"
                "class Inner extends InnerBase;\n"
                "  function new();\n"
                "    super.new(3);\n"
                "  endfunction\n"
                "endclass\n"
                "class OuterBase;\n"
                "  int w;\n"
                "  function new(int a);\n"
                "    w = a;\n"
                "  endfunction\n"
                "endclass\n"
                "class Outer extends OuterBase;\n"
                "  Inner child;\n"
                "  function new();\n"
                "    super.new(5);\n"
                "    child = new;\n"
                "  endfunction\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    Outer o;\n"
                "    o = new;\n"
                "    result = o.w * 100 + InnerBase::runs * 10 + o.child.v;\n"
                "  end\n"
                "endmodule\n",
                "result"),
      513u);
}

// §8.15 has super.new be the first statement of the constructor, and A.2.8
// puts a body's local declarations ahead of its statements, so a constructor
// that declares a local before its `super.new("__top__", null)` still makes
// that call its base constructor call -- uvm_root::new's shape, where the
// base takes the root path only for that name. With the declaration counted
// as the first statement the base ran with no arguments and no name.
TEST(ClassConstructorSim, LocalDeclarationAheadOfLeadingSuperNew) {
  EXPECT_EQ(RunAndGet("class base;\n"
                      "  int is_root;\n"
                      "  function new(string name, base parent);\n"
                      "    if (parent == null && name == \"__top__\") "
                      "is_root = 7;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class root extends base;\n"
                      "  int seen;\n"
                      "  extern function new();\n"
                      "endclass\n"
                      "function root::new();\n"
                      "  int scratch;\n"
                      "  super.new(\"__top__\", null);\n"
                      "  scratch = 3;\n"
                      "  seen = scratch;\n"
                      "endfunction\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    root r;\n"
                      "    r = new;\n"
                      "    result = r.is_root * 10 + r.seen;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            73u);
}

// §8.7: a class-typed property with the declaration initializer `= new` holds
// an object constructed when the enclosing object is, with that object's own
// initializers run -- §8.12's example, `baseA a = new;` in B, where baseA's j
// is 5. The result packs `b1.a.j` and `b1.i`; an initializer that constructed
// nothing read j as 0, giving 1 where 51 is expected.
TEST(ClassConstructorSim, ClassTypedPropertyNewInitializerConstructsItsObject) {
  EXPECT_EQ(RunAndGet("class baseA;\n"
                      "  int j = 5;\n"
                      "endclass\n"
                      "class B;\n"
                      "  int i = 1;\n"
                      "  baseA a = new;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    B b1;\n"
                      "    b1 = new;\n"
                      "    result = b1.a.j * 10 + b1.i;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            51u);
}

// §8.7: the arguments of a property's `= new(...)` initializer are passed to
// the constructor of the property's class, and that class's own property
// initializers have run when its constructor body reads them: `new(7)` adds
// 7 to the 5 baseA's j starts at. A construction that dropped the argument
// would read 5, one that skipped the constructor body 5, and one that ran the
// body before the initializers 7.
TEST(ClassConstructorSim, ClassTypedPropertyNewInitializerBindsItsArguments) {
  EXPECT_EQ(RunAndGet("class baseA;\n"
                      "  int j = 5;\n"
                      "  function new(int v);\n"
                      "    j = j + v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class B;\n"
                      "  baseA a = new(7);\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    B b1;\n"
                      "    b1 = new;\n"
                      "    result = b1.a.j;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            12u);
}

// §8.12: a shallow copy `b2 = new b1` copies b1's handles and not the objects
// they name, so the baseA that b1's property initializer constructed is the
// one object behind both `b1.a` and `b2.a`: writing `b2.a.j = 50` is seen
// through `b1.a.j`, the two handles compare equal, and b1's own `i` keeps 1
// beside b2's 10. The result packs `b1.a.j`, `b1.i` and the comparison; an
// initializer that constructed nothing left the write unseen, giving 11.
TEST(ClassConstructorSim,
     ShallowCopySharesTheObjectAPropertyInitializerConstructed) {
  EXPECT_EQ(
      RunAndGet("class baseA;\n"
                "  int j = 5;\n"
                "endclass\n"
                "class B;\n"
                "  int i = 1;\n"
                "  baseA a = new;\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    B b1, b2;\n"
                "    b1 = new;\n"
                "    b2 = new b1;\n"
                "    b2.i = 10;\n"
                "    b2.a.j = 50;\n"
                "    result = b1.a.j * 100 + b1.i * 10 + (b1.a == b2.a);\n"
                "  end\n"
                "endmodule\n",
                "result"),
      5011u);
}

// §8.7 gives a constructor's arguments the conventions of any other subroutine
// call, and §13.5 has the return copy an output formal into the call's
// variable: after `a = new(ia)` with the constructor writing `oid = m_id`, the
// caller's `ia` holds what the object's `id` holds. The counter starts at 3 so
// an output formal never copied out, which leaves `ia` at 0, reads 3 rather
// than 33.
TEST(ClassConstructorSim, OutputFormalOfNewIsCopiedOutToTheCallersVariable) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  static local int m_id = 3;\n"
                      "  int id;\n"
                      "  function new(output int oid);\n"
                      "    oid = m_id;\n"
                      "    id = m_id;\n"
                      "    m_id++;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int ia;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base a;\n"
                      "    a = new(ia);\n"
                      "    result = ia * 10 + a.id;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            33u);
}

// §8.7 and §13.5: each `new(...)` call copies the output formal into its own
// actual, so two constructions leave `ia` at 0 and `ib` at 1, the values of
// `a.id` and `b.id`; the four are packed as one integer, and a copy-out that
// never happened leaves `ib` at 0, reading 1 rather than 101.
TEST(ClassConstructorSim, OutputFormalOfNewIsCopiedOutOnEachConstruction) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  static local int m_id = 0;\n"
                      "  int id;\n"
                      "  function new(output int oid);\n"
                      "    oid = m_id;\n"
                      "    id = m_id;\n"
                      "    m_id++;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int ia, ib;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base a, b;\n"
                      "    a = new(ia);\n"
                      "    b = new(ib);\n"
                      "    result = ia * 1000 + ib * 100 + a.id * 10 + b.id;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            101u);
}

// §8.7 and §8.15: a subclass constructor passing its own output formal to
// `super.new(oid)` receives the base constructor's value in that formal when
// the base returns, and copies it out to the caller in turn when it returns
// itself, so `ic` reads the 5 the base counter held; the subclass adds 100 to
// what came back before it returns, telling a copy made at the base level from
// one made at the outer level alone. A chain copying out at neither level
// leaves `ic` at 0, reading 5 rather than 1055.
TEST(ClassConstructorSim,
     OutputFormalOfNewIsCopiedOutThroughASubclassSuperNewCall) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  static local int m_id = 5;\n"
                      "  int id;\n"
                      "  function new(output int oid);\n"
                      "    oid = m_id;\n"
                      "    id = m_id;\n"
                      "    m_id++;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class D extends Base;\n"
                      "  function new(output int oid);\n"
                      "    super.new(oid);\n"
                      "    oid = oid + 100;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int ic;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D c;\n"
                      "    c = new(ic);\n"
                      "    result = ic * 10 + c.id;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1055u);
}

// §8.17: a subclass constructor declared `new(default)` forwards the caller's
// trailing actuals to the base constructor, so the base's output formal is
// bound from the caller's `ic` and copied out to it when the base returns,
// with the subclass's own scope still on the stack between them; the third
// construction leaves `ic` at 2 beside `c.id`, reading 22 rather than 2.
TEST(ClassConstructorSim,
     OutputFormalOfNewIsCopiedOutThroughASubclassDefaultArgument) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  static local int m_id = 0;\n"
                      "  int id;\n"
                      "  function new(output int oid);\n"
                      "    oid = m_id;\n"
                      "    id = m_id;\n"
                      "    m_id++;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class A extends Base;\n"
                      "  function new(default);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int ia, ib, ic;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base a, b;\n"
                      "    A c;\n"
                      "    a = new(ia);\n"
                      "    b = new(ib);\n"
                      "    c = new(ic);\n"
                      "    result = ic * 10 + c.id;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            22u);
}

}  // namespace
