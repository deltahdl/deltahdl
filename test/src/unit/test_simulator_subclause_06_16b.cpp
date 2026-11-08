#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(StringMethodReceivers, PropertyThroughAHandleAndBareInsideAMethod) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    string s = \"hello\";\n"
                       "    function int l(); return s.len(); endfunction\n"
                       "  endclass\n"
                       "  C h;\n"
                       "  initial begin\n"
                       "    h = new;\n"
                       "    $display(\"len=%0d up=%s in=%0d\", h.s.len(),\n"
                       "             h.s.toupper(), h.l());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "len=5 up=HELLO in=5\n");
}

TEST(StringMethodReceivers, PropertyThroughThisInsideAMethod) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  class C;\n"
                 "    string s = \"hello\";\n"
                 "    function string up(); return this.s.toupper();\n"
                 "    endfunction\n"
                 "    function int n(); return this.s.len(); endfunction\n"
                 "  endclass\n"
                 "  C h;\n"
                 "  initial begin\n"
                 "    h = new;\n"
                 "    $display(\"up=%s n=%0d\", h.up(), h.n());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "up=HELLO n=5\n");
}

TEST(StringMethodReceivers, EveryValueMethodOnAProperty) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  class C; string s = \"hello\"; endclass\n"
                 "  C h;\n"
                 "  initial begin\n"
                 "    h = new;\n"
                 "    $display(\"len=%0d up=%s lo=%s sub=%s g=%0d\",\n"
                 "             h.s.len(), h.s.toupper(),\n"
                 "             h.s.toupper().tolower(), h.s.substr(1,3),\n"
                 "             h.s.getc(1));\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "len=5 up=HELLO lo=hello sub=ell g=101\n");
}

TEST(StringMethodReceivers, ConversionsOnAProperty) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  class C; string n; endclass\n"
                 "  C h;\n"
                 "  initial begin\n"
                 "    h = new;\n"
                 "    h.n = \"123\"; $write(\"atoi=%0d \", h.n.atoi());\n"
                 "    h.n = \"ff\"; $write(\"hex=%0d \", h.n.atohex());\n"
                 "    h.n = \"10\"; $write(\"oct=%0d \", h.n.atooct());\n"
                 "    h.n = \"101\"; $write(\"bin=%0d \", h.n.atobin());\n"
                 "    h.n = \"2.5\"; $display(\"real=%f\", h.n.atoreal());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "atoi=123 hex=255 oct=8 bin=5 real=2.500000\n");
}

TEST(StringMethodReceivers, CompareOfAPropertyWithAProperty) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  class C;\n"
                 "    string s;\n"
                 "    function new(string v); s = v; endfunction\n"
                 "  endclass\n"
                 "  C a, b;\n"
                 "  initial begin\n"
                 "    a = new(\"abc\"); b = new(\"abd\");\n"
                 "    $display(\"cmp=%0d icmp=%0d\", b.s.compare(a.s) > 0,\n"
                 "             a.s.icompare(\"ABC\"));\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "cmp=1 icmp=0\n");
}

TEST(StringMethodReceivers, StaticPropertyScopedAndBareInAStaticMethod) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  class C;\n"
                 "    static string name = \"name\";\n"
                 "    static function int len(); return name.len();\n"
                 "    endfunction\n"
                 "    static function string up(); return name.toupper();\n"
                 "    endfunction\n"
                 "  endclass\n"
                 "  initial begin\n"
                 "    $display(\"n=%0d up=%s first=%s\", C::len(), C::up(),\n"
                 "             C::name.substr(0,0));\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "n=4 up=NAME first=n\n");
}

TEST(StringMethodReceivers, InputStringFormal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  function automatic int f(input string s);\n"
                       "    $display(\"in=%0d UP=%s\", s.len(), s.toupper());\n"
                       "    return s.len();\n"
                       "  endfunction\n"
                       "  string s = \"world\";\n"
                       "  int n;\n"
                       "  initial begin\n"
                       "    n = f(s);\n"
                       "    $display(\"n=%0d\", n);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "in=5 UP=WORLD\nn=5\n");
}

TEST(StringMethodReceivers, OutputStringFormal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  function automatic void h(output string o);\n"
                       "    o = \"abc-\";\n"
                       "    $display(\"out=%0d %s\", o.len(), o.toupper());\n"
                       "  endfunction\n"
                       "  string o;\n"
                       "  initial begin\n"
                       "    h(o);\n"
                       "    $display(\"o=%s\", o);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "out=4 ABC-\no=abc-\n");
}

TEST(StringMethodReceivers, PackageStringImportedAndScoped) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package P;\n"
                       "  string ps = \"name\";\n"
                       "endpackage\n"
                       "module t;\n"
                       "  import P::*;\n"
                       "  initial begin\n"
                       "    $display(\"len=%0d up=%s q=%s sub=%s\", ps.len(),\n"
                       "             ps.toupper(), P::ps.toupper(),\n"
                       "             ps.substr(1,2));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "len=4 up=NAME q=NAME sub=am\n");
}

TEST(StringMethodReceivers, MethodOnACallResultAndOnAMethodResult) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  class C;\n"
                 "    string s = \"hello\";\n"
                 "    function string get(); return s; endfunction\n"
                 "    function int l(); return s.len(); endfunction\n"
                 "  endclass\n"
                 "  string s = \"hello world\";\n"
                 "  C h;\n"
                 "  initial begin\n"
                 "    h = new;\n"
                 "    $display(\"a=%0d b=%s c=%s d=%0d e=%s\",\n"
                 "             s.toupper().substr(0,2).len(),\n"
                 "             h.s.substr(1,3).toupper(),\n"
                 "             h.get().substr(0,2),\n"
                 "             h.get().toupper().getc(0),\n"
                 "             s.substr(6,10).toupper().substr(0,2));\n"
                 "    $display(\"f=%0d g=%0d l=%0d\", h.get().len(),\n"
                 "             h.s.toupper().tolower().substr(2,4).len(),\n"
                 "             h.l());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "a=3 b=ELL c=hel d=72 e=WOR\nf=5 g=3 l=5\n");
}

TEST(StringMethodReceivers, AStringPropertyOfACallsResultTakesStringMethods) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class K;\n"
                       "    string s = \"ab\"; string u = \"xyz\"; int n = 7;\n"
                       "  endclass\n"
                       "  K k = new;\n"
                       "  function K f(); return k; endfunction\n"
                       "  initial $display(\"%0d %s %0d\", f().s.len(),\n"
                       "                   f().u.toupper(), f().n);\n"
                       "endmodule\n",
                       f),
            "2 XYZ 7\n");
}

TEST(StringMethodReceivers, AStringTypedefPropertyTakesStringMethods) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef string str_t;\n"
                       "  class K; str_t u = \"xyz\"; endclass\n"
                       "  K k = new;\n"
                       "  function K f(); return k; endfunction\n"
                       "  initial $display(\"%s %s\", f().u.toupper(),\n"
                       "                   k.u.toupper());\n"
                       "endmodule\n",
                       f),
            "XYZ XYZ\n");
}

TEST(StringMethodReceivers, ClassMethodsNamedLikeStringMethodsAreTheClasss) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    function int len(); return 7; endfunction\n"
                       "    static function int substr(int a, int b);\n"
                       "      return a + b;\n"
                       "    endfunction\n"
                       "  endclass\n"
                       "  class D; C c; endclass\n"
                       "  C h; D d;\n"
                       "  initial begin\n"
                       "    h = new; d = new; d.c = h;\n"
                       "    $display(\"%0d %0d %0d\", h.len(), d.c.len(),\n"
                       "             C::substr(1, 2));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "7 7 3\n");
}

TEST(StringMethodReceivers, MethodOnAModuleFunctionResult) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  function automatic string tag(string s);\n"
                 "    return {s, \"2\"};\n"
                 "  endfunction\n"
                 "  initial $display(\"n=%0d up=%s\", tag(\"ab\").len(),\n"
                 "                   tag(\"ab\").toupper());\n"
                 "endmodule\n",
                 f),
      "n=3 up=AB2\n");
}

TEST(StringMethodReceivers, PropertyAfterADelayInATaskOfTheClass) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    string s = \"abc\";\n"
                       "    task run();\n"
                       "      #5 s = {s, \"XY\"};\n"
                       "      $display(\"t=%0t len=%0d\", $time, s.len());\n"
                       "      #5 s = s.toupper();\n"
                       "      $display(\"t=%0t s=%s\", $time, s);\n"
                       "    endtask\n"
                       "  endclass\n"
                       "  C h;\n"
                       "  initial begin h = new; h.run(); end\n"
                       "endmodule\n",
                       f),
            "t=5 len=5\nt=10 s=ABCXY\n");
}

TEST(StringMethodReceivers, PropertyThroughAChainOfHandles) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C; string s = \"abc\"; endclass\n"
                       "  class D; C c; endclass\n"
                       "  D d;\n"
                       "  initial begin\n"
                       "    d = new; d.c = new;\n"
                       "    $display(\"len=%0d up=%s\", d.c.s.len(),\n"
                       "             d.c.s.toupper());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "len=3 up=ABC\n");
}

TEST(StringMethodReceivers, PutcAndIndexedWriteOnAPropertyThroughAHandle) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C; string p = \"abz\"; endclass\n"
                       "  C h;\n"
                       "  initial begin\n"
                       "    h = new; h.p[0] = \"x\"; h.p.putc(1, \"y\");\n"
                       "    $display(\"prop=%s\", h.p);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "prop=xyz\n");
}

TEST(StringMethodReceivers, ConversionsIntoAPropertyInsideAMethod) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    string n;\n"
                       "    function void conv();\n"
                       "      n.itoa(42); $write(\"itoa=%s \", n);\n"
                       "      n.hextoa(255); $write(\"hextoa=%s \", n);\n"
                       "      n.octtoa(15); $write(\"octtoa=%s \", n);\n"
                       "      n.bintoa(5); $write(\"bintoa=%s \", n);\n"
                       "      n.realtoa(1.5); $display(\"realtoa=%s\", n);\n"
                       "    endfunction\n"
                       "  endclass\n"
                       "  C h;\n"
                       "  initial begin\n"
                       "    h = new; h.n = \"2.5\"; h.conv();\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "itoa=42 hextoa=ff octtoa=17 bintoa=101 realtoa=1.5\n");
}

TEST(StringMethodReceivers, PutcThroughThisAndIndexedWriteBareInsideAMethod) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    string s = \"hello\";\n"
                       "    function void fix(); this.s.putc(1, \"a\");\n"
                       "      s[4] = \"!\"; endfunction\n"
                       "  endclass\n"
                       "  C h;\n"
                       "  initial begin\n"
                       "    h = new; h.fix();\n"
                       "    $display(\"put=%s\", h.s);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "put=hall!\n");
}

TEST(StringMethodReceivers, PutcScopedAndItoaBareOnAStaticProperty) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    static string name = \"name\";\n"
                       "    static function void num(); name.itoa(7);\n"
                       "    endfunction\n"
                       "  endclass\n"
                       "  initial begin\n"
                       "    C::name.putc(0, \"N\");\n"
                       "    $display(\"%s\", C::name);\n"
                       "    C::num();\n"
                       "    $display(\"%s\", C::name);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "Name\n7\n");
}

TEST(StringMethodReceivers, ItoaIntoAnOutputStringFormal) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  function automatic void h(output string o, input int n);\n"
          "    o = \"abc\"; o = {o, \"-\"}; o.itoa(n); o = {\"abc-\", o};\n"
          "    $display(\"out=%s\", o);\n"
          "  endfunction\n"
          "  string o;\n"
          "  initial begin\n"
          "    h(o, 3);\n"
          "    $display(\"o=%s\", o);\n"
          "  end\n"
          "endmodule\n",
          f),
      "out=abc-3\no=abc-3\n");
}

TEST(StringMethodReceivers, ElementOfAStringArray) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string m[$];\n"
                       "  string a[2];\n"
                       "  string d[];\n"
                       "  initial begin\n"
                       "    m.push_back(\"hello\"); m.push_back(\"ok\");\n"
                       "    a[1] = \"abc\"; d = new[1]; d[0] = \"wxyz\";\n"
                       "    $display(\"%0d %0d %0d %0d %s %s\", m[0].len(),\n"
                       "             m[1].len(), a[1].len(), d[0].len(),\n"
                       "             m[0].toupper(), a[1].toupper());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5 2 3 4 HELLO ABC\n");
}

TEST(StringMethodReceivers, ElementOfAStringQueueProperty) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  class C;\n"
                 "    string names[$];\n"
                 "    function void fill(); names.push_back(\"hello\");\n"
                 "      names.push_back(\"world\"); endfunction\n"
                 "    function int l(); return names[1].len(); endfunction\n"
                 "  endclass\n"
                 "  C h;\n"
                 "  initial begin\n"
                 "    h = new; h.fill();\n"
                 "    $display(\"%0d %0d %s\", h.l(), h.names[0].len(),\n"
                 "             h.names[1].toupper());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "5 5 WORLD\n");
}

TEST(StringMethodReceivers, CharacterWriteIntoAnElementOfAStringArrayProperty) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class C;\n"
                 "  string inst[2];\n"
                 "  static string names[1];\n"
                 "  string sd[];\n"
                 "  function void m(); inst[1] = \"cd\"; inst[1][0] = \"Y\"; "
                 "endfunction\n"
                 "endclass\n"
                 "module t;\n"
                 "  C h;\n"
                 "  initial begin\n"
                 "    h = new; h.m();\n"
                 "    h.inst[0] = \"ab\"; h.inst[0][1] = \"X\";\n"
                 "    C::names[0] = \"st\"; C::names[0][1] = \"T\";\n"
                 "    h.sd = new[1]; h.sd[0] = \"dy\"; h.sd[0][0] = \"D\";\n"
                 "    $display(\"%s %s %s %s\", h.inst[1], h.inst[0], "
                 "C::names[0], h.sd[0]);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "Yd aX sT Dy\n");
}

TEST(StringMethodReceivers, ElementOfATypedefStringQueueProperty) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("typedef string sq_t[$];\n"
                 "class C;\n"
                 "  sq_t tq;\n"
                 "endclass\n"
                 "module t;\n"
                 "  C h;\n"
                 "  initial begin\n"
                 "    h = new; h.tq.push_back(\"t0\");\n"
                 "    $display(\"%0d %s\", h.tq[0].len(), h.tq[0].toupper());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "2 T0\n");
}

}  // namespace
