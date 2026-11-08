#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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

TEST(EnumMethodReceivers, MemberLiteral) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  enum integer {IDLE, S1, S2} state;\n"
                       "  initial $display(\"n=%s\", IDLE.next().name());\n"
                       "endmodule\n",
                       f),
            "n=S1\n");
}

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

TEST(EnumMethodOnAnArrayElement, OnPackedAndUnpackedElements) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  enum bit [1:0] {A, B, C} [3:0] v;\n"
          "  typedef enum {P, Q, R} e_t;\n"
          "  e_t arr [3];\n"
          "  initial begin\n"
          "    v[1] = B; v[2] = C; arr[1] = R;\n"
          "    $display(\"%s %s %s %s\", v[1].name(), v[2].next().name(),\n"
          "             arr[1].name(), arr[1].prev().name());\n"
          "  end\n"
          "endmodule\n",
          f),
      "B A R Q\n");
}

TEST(EnumMethodOnAnArrayElement, ElementIsOfTheEnumWhereverItsTypeIsAsked) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  enum bit [1:0] {A, B, C} [1:0] v;\n"
          "  enum bit [1:0] {X, Y, Z} c;\n"
          "  int ia [2];\n"
          "  int ok1, ok2, ok3, n1, t1, n2, t2;\n"
          "  covergroup ge; coverpoint v[0]; endgroup\n"
          "  covergroup gb; coverpoint c[0]; endgroup\n"
          "  ge e = new;\n"
          "  gb b = new;\n"
          "  initial begin\n"
          "    ok1 = $cast(v[1], 2);\n"
          "    ok2 = $cast(v[0], 3);\n"
          "    ok3 = $cast(ia[0], 5);\n"
          "    c = Y;\n"
          "    e.sample(); b.sample();\n"
          "    void'(e.get_inst_coverage(n1, t1));\n"
          "    void'(b.get_inst_coverage(n2, t2));\n"
          "    $display(\"%0d %0d %0d %h %0d %0d/%0d %0d/%0d\", ok1, ok2,\n"
          "             ok3, v, ia[0], n1, t1, n2, t2);\n"
          "  end\n"
          "endmodule\n",
          f),
      "1 0 1 8 5 1/3 1/2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
