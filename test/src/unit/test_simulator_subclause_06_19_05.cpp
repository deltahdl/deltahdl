// §6.19.5 (printed pages 123-124) declares first(), last(), next(), prev(),
// num() and name() on the enumerated type, so each is called on any expression
// of an enumeration type, wherever the type and the expression are declared:
// a class property named through a handle or a chain of them (§8.3), bare or
// through `this` inside a method (§8.11), a static property named `C::se`
// (§8.9), a property the parent class declares named through `super.` (§8.15),
// a nested class's property (§8.23), a package's variable, parameter, member
// literal and function result (§26.3), a subroutine formal (§13.3, §13.4), a
// class localparam through a specialization (§8.25), a variable of a
// class-scoped enum typedef (§8.23), a member literal, and a property read
// after a task's timing control. Each case prints what the standard predicts
// and reads the simulator's output whole, so a method that answered "" or 0
// for a receiver it did not recognise as an enumeration fails on the value. A
// module-scope enum variable and a method's local are the two receivers that
// always worked, so every case names its receiver some other way.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §6.19.5.6 and §6.19.5.3 on a property named through a handle, `h.e.name()`,
// and chained, `h.e.next().name()`.
TEST(EnumMethodReceivers, PropertyThroughAHandle) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef enum {red, green, blue} Colors;\n"
                       "  class C; Colors e = green; endclass\n"
                       "  C h;\n"
                       "  initial begin\n"
                       "    h = new;\n"
                       "    $display(\"n=%s v=%0d nn=%s\", h.e.name(), h.e,\n"
                       "             h.e.next().name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=green v=1 nn=blue\n");
}

// §8.11: `this.e.next()` inside a method; §8.3: a chain of handles `d.c.e`
// with three next() calls; §8.9: the static property as `C::se`; §6.19.5.5
// and §6.19.5.2 on a property.
TEST(EnumMethodReceivers, ThisChainedHandlesAndStaticProperty) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  typedef enum {red, green, blue, yellow} Colors;\n"
          "  class C;\n"
          "    Colors e;\n"
          "    static Colors se;\n"
          "    function Colors nxt(); return this.e.next(); endfunction\n"
          "  endclass\n"
          "  class D; C c; endclass\n"
          "  C h; D d;\n"
          "  initial begin\n"
          "    h = new; h.e = green; d = new; d.c = h;\n"
          "    $display(\"this=%s hn=%s hnn=%s chain=%s\", h.e.name(),\n"
          "             h.nxt().name(), h.e.next().next().name(),\n"
          "             d.c.e.next().next().next().name());\n"
          "    C::se = yellow;\n"
          "    $display(\"static=%s sn=%s cnt=%0d last=%s\", C::se.name(),\n"
          "             C::se.next().name(), h.e.num(), d.c.e.last().name());\n"
          "  end\n"
          "endmodule\n",
          f),
      "this=green hn=blue hnn=yellow chain=red\n"
      "static=yellow sn=red cnt=4 last=yellow\n");
}

// §6.19.5.7's own loop written over a bare property inside a method: `e` is
// the object's property, first(), last() and next() are called on the local
// `k` and name() on it, and the walk visits every member once.
TEST(EnumMethodReceivers, LoopOverABarePropertyInsideAMethod) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef enum {red, green, blue, yellow} Colors;\n"
                       "  class C;\n"
                       "    Colors e;\n"
                       "    function string walk();\n"
                       "      string s = \"loop:\"; Colors k;\n"
                       "      k = e.first();\n"
                       "      forever begin\n"
                       "        s = {s, \" \", k.name()};\n"
                       "        if (k == k.last()) break;\n"
                       "        k = k.next();\n"
                       "      end\n"
                       "      return s;\n"
                       "    endfunction\n"
                       "  endclass\n"
                       "  C h;\n"
                       "  initial begin\n"
                       "    h = new; h.e = green;\n"
                       "    $display(\"%s\", h.walk());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "loop: red green blue yellow\n");
}

// §26.3: a package's enum variable named `P::pc` and by its imported bare
// name `pc`, its member literal `P::RED`, and the result of its function
// `after(v)`; §6.19.5.1 and §6.19.5.2 on the imported variable.
TEST(EnumMethodReceivers, PackageVariableLiteralAndFunctionResult) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "package P;\n"
          "  typedef enum {RED, GREEN, BLUE} color_t;\n"
          "  color_t pc = GREEN;\n"
          "  function automatic color_t after(color_t c); return c.next();\n"
          "  endfunction\n"
          "endpackage\n"
          "module t;\n"
          "  import P::*;\n"
          "  color_t v = GREEN;\n"
          "  initial begin\n"
          "    $display(\"v=%s n=%s q=%s f=%s l=%s\", v.name(),\n"
          "             after(v).name(), P::RED.name(), v.first().name(),\n"
          "             v.last().name());\n"
          "    P::pc = P::pc.next();\n"
          "    $display(\"pk=%s pkn=%s num=%0d cmp=%0d\", P::pc.name(),\n"
          "             P::pc.next().name(), pc.num(), pc == BLUE);\n"
          "  end\n"
          "endmodule\n",
          f),
      "v=GREEN n=BLUE q=RED f=RED l=BLUE\n"
      "pk=BLUE pkn=RED num=3 cmp=1\n");
}

// §26.3 with §8.3: a property declared with a package's enum typedef, named
// through a handle.
TEST(EnumMethodReceivers, PropertyOfAPackageEnumType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package P;\n"
                       "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  import P::*;\n"
                       "  class C; color_t e; endclass\n"
                       "  C c;\n"
                       "  initial begin\n"
                       "    c = new; c.e = GREEN;\n"
                       "    $display(\"e=%s n=%0d\", c.e.name(), c.e);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "e=GREEN n=1\n");
}

// §13.3 and §13.4: an input formal `c.next().name()`, a ref formal and an
// output formal advanced by `c = c.next()`, a function's result `fret().name()`
// and a local advanced then named.
TEST(EnumMethodReceivers, SubroutineFormalsAndResult) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  typedef enum {red, green, blue, yellow} Colors;\n"
          "  function automatic string fin(input Colors c);\n"
          "    return c.next().name();\n"
          "  endfunction\n"
          "  task automatic tref(ref Colors c); c = c.next(); endtask\n"
          "  function automatic void fout(output Colors c);\n"
          "    c = red; c = c.next();\n"
          "  endfunction\n"
          "  function automatic Colors fret();\n"
          "    Colors l; l = yellow; return l.next();\n"
          "  endfunction\n"
          "  function automatic string floc();\n"
          "    Colors l; l = green; l = l.next(); return l.name();\n"
          "  endfunction\n"
          "  Colors a = green, b = blue, o;\n"
          "  initial begin\n"
          "    tref(b); fout(o);\n"
          "    $display(\"in=%s ref=%s out=%s ret=%s local=%s\", fin(a),\n"
          "             b.name(), o.name(), fret().name(), floc());\n"
          "  end\n"
          "endmodule\n",
          f),
      "in=blue ref=yellow out=green ret=red local=blue\n");
}

// §8.25 with §6.20.4: a class localparam of the enum type, named through a
// specialization of the class, `P#(X)::LC.name()`.
TEST(EnumMethodReceivers, ClassLocalparamThroughASpecialization) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef enum {red, green, blue} Colors;\n"
                       "  class X; endclass\n"
                       "  class P #(type C = X);\n"
                       "    localparam Colors LC = green;\n"
                       "  endclass\n"
                       "  initial $display(\"c=%s\", P#(X)::LC.name());\n"
                       "endmodule\n",
                       f),
            "c=green\n");
}

// §6.24.2 with §8.3: a property `$cast` wrote inside a method, named through
// a handle afterwards.
TEST(EnumMethodReceivers, PropertyWrittenByDynamicCast) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef enum {red, green, blue} Colors;\n"
                 "  class C;\n"
                 "    Colors c;\n"
                 "    function bit try(int v); return $cast(c, v);\n"
                 "    endfunction\n"
                 "  endclass\n"
                 "  C h;\n"
                 "  initial begin\n"
                 "    h = new;\n"
                 "    $display(\"prop=%0d pcol=%s\", h.try(1), h.c.name());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "prop=1 pcol=green\n");
}

// §26.3 with §13.4: the result of a package function named `P::toc(2)`,
// whose declared type is the package's enumeration.
TEST(EnumMethodReceivers, ScopedPackageFunctionResult) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package P;\n"
                 "  typedef enum {red, green, blue} Colors;\n"
                 "  function automatic Colors toc(int v); return Colors'(v);\n"
                 "  endfunction\n"
                 "endpackage\n"
                 "module t;\n"
                 "  import P::*;\n"
                 "  initial $display(\"pe=%s\", P::toc(2).name());\n"
                 "endmodule\n",
                 f),
      "pe=blue\n");
}

// §8.23 and §8.15: a property of a class-scoped enum typedef through a derived
// class's handle, through `super.` inside the derived class's method, and a
// nested class's property through a handle and bare inside its own method;
// §6.19.5.4 and §6.19.5.5 on the nested class's property.
TEST(EnumMethodReceivers, NestedClassAndSuper) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  class Outer;\n"
          "    typedef enum {B0, B1, B2} b_t;\n"
          "    b_t b = B1;\n"
          "    class Nested;\n"
          "      typedef enum {N0, N1} n_t;\n"
          "      n_t n = N1;\n"
          "      function string prevname(); return n.prev().name();\n"
          "      endfunction\n"
          "    endclass\n"
          "  endclass\n"
          "  class Derived extends Outer;\n"
          "    function string supname(); return super.b.next().name();\n"
          "    endfunction\n"
          "  endclass\n"
          "  Derived d; Outer::Nested nn;\n"
          "  initial begin\n"
          "    d = new; nn = new;\n"
          "    $display(\"base=%s sup=%s nested=%s nn=%s cnt=%0d\", "
          "d.b.name(),\n"
          "             d.supname(), nn.n.name(), nn.prevname(), nn.n.num());\n"
          "  end\n"
          "endmodule\n",
          f),
      "base=B1 sup=B2 nested=N1 nn=N0 cnt=2\n");
}

// §8.23: a module variable declared with a class-scoped enum typedef,
// `C::e_t en`, names its member.
TEST(EnumMethodReceivers, VariableOfAClassScopedEnumTypedef) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    typedef enum {ZERO, ONE, TWO} e_t;\n"
                       "  endclass\n"
                       "  C::e_t en;\n"
                       "  initial begin\n"
                       "    en = C::e_t'(2);\n"
                       "    $display(\"en=%s\", en.name());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "en=TWO\n");
}

// §26.3 with §6.20: a package parameter of the package's enum type, named
// bare through a wildcard import.
TEST(EnumMethodReceivers, PackageParameter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package P;\n"
                       "  typedef enum {RED, GREEN} color_t;\n"
                       "  parameter color_t EC = GREEN;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  import P::*;\n"
                       "  initial $display(\"EC=%s\", EC.name());\n"
                       "endmodule\n",
                       f),
            "EC=GREEN\n");
}

// §6.19 with §6.19.5.3: a member literal is an expression of its enumeration's
// type, so `IDLE.next().name()` names the member after IDLE, for an
// enumeration declared on the variable itself rather than by a typedef.
TEST(EnumMethodReceivers, MemberLiteral) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  enum integer {IDLE, S1, S2} state;\n"
                       "  initial $display(\"n=%s\", IDLE.next().name());\n"
                       "endmodule\n",
                       f),
            "n=S1\n");
}

// §13.3: a property named bare in a task of the class after each of its
// timing controls, advanced by `e = e.next()` between them.
TEST(EnumMethodReceivers, PropertyAfterADelayInATask) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef enum {red, green, blue, yellow} Colors;\n"
                       "  class C;\n"
                       "    Colors e = green;\n"
                       "    task run();\n"
                       "      $display(\"t=%0t e=%s\", $time, e.name());\n"
                       "      #5 e = e.next();\n"
                       "      $display(\"t=%0t e=%s\", $time, e.name());\n"
                       "      #5 e = e.next();\n"
                       "      $display(\"t=%0t e=%s\", $time, e.name());\n"
                       "    endtask\n"
                       "  endclass\n"
                       "  C h;\n"
                       "  initial begin h = new; h.run(); end\n"
                       "endmodule\n",
                       f),
            "t=0 e=green\nt=5 e=blue\nt=10 e=yellow\n");
}

// §6.24.1 with A.8.4: a static cast to the enumeration is a primary of that
// type, so §6.19.5.6's name() is called on it: `Cols'(Su)` holds Su's 6,
// which is no member of Cols, so name() answers the empty string (§6.19.5.6),
// and `Cols'(2)` holds Blue; `Cols'(1).next.name` chains without parentheses
// (§6.19.5.7).
TEST(EnumMethodReceivers, StaticCastResult) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef enum {Red, Green, Blue} Cols;\n"
                 "  typedef enum {Mo, Tu, We, Th, Fr, Sa, Su} Week;\n"
                 "  initial begin\n"
                 "    $display(\"name=[%s] n2=%s nn=%s\", Cols'(Su).name(),\n"
                 "             Cols'(2).name(), Cols'(1).next.name);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "name=[] n2=Blue nn=Blue\n");
}

// §6.19.5.7 (printed page 124) writes its own example with `c.first`,
// `c.name`, `c.last` and `c.next` and no argument list, the form A.8.6's
// method_call_body admits for a method taking no arguments: each of the six
// methods on a module-scope variable, spelled without parentheses.
TEST(EnumMethodWithoutArgumentList, EveryMethodOnAVariable) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef enum {red, green, blue, yellow} Colors;\n"
                 "  Colors c;\n"
                 "  initial begin\n"
                 "    c = blue;\n"
                 "    $display(\"name=%s next=%0d prev=%0d first=%0d last=%0d "
                 "num=%0d val=%0d\",\n"
                 "             c.name, c.next, c.prev, c.first, c.last, c.num,"
                 " c);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "name=blue next=3 prev=1 first=0 last=3 num=4 val=2\n");
}

// §6.19.5.7's loop as the subclause writes it, over a variable initialized
// with `c.first`, visiting every member once and stopping at `c.last`.
TEST(EnumMethodWithoutArgumentList, TheSubclausesOwnLoop) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef enum {red, green, blue, yellow} Colors;\n"
                       "  Colors c = c.first;\n"
                       "  initial begin\n"
                       "    forever begin\n"
                       "      $display(\"%s : %0d\", c.name, c);\n"
                       "      if (c == c.last) break;\n"
                       "      c = c.next;\n"
                       "    end\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "red : 0\ngreen : 1\nblue : 2\nyellow : 3\n");
}

// The argument-list-free form on a property through a handle, `h.e.name`, on
// a bare property inside a method, and chained, `c.next.name` and
// `h.e.next.next.name`, since §6.19.5.3 gives next() the enumeration's type.
TEST(EnumMethodWithoutArgumentList, OnAPropertyAndChained) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef enum {red, green, blue, yellow} Colors;\n"
                 "  class C;\n"
                 "    Colors e = green;\n"
                 "    function string nn(); return e.next.name; endfunction\n"
                 "  endclass\n"
                 "  C h; Colors c = yellow;\n"
                 "  initial begin\n"
                 "    h = new;\n"
                 "    $display(\"p=%s pn=%s cn=%s hnn=%s\", h.e.name, h.nn(),\n"
                 "             c.next.name, h.e.next.next.name);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "p=green pn=blue cn=red hnn=yellow\n");
}

}  // namespace
