// §6.16 (printed page 112) declares the string methods of §6.16.1 through
// §6.16.15 on the string type, so each is called on any expression of that
// type: a class property named through a handle (§8.3), by its bare name or
// through `this` (§8.11) inside a method, a static property named `C::name`
// (§8.9, §8.10) or bare inside a static method, a subroutine formal (§13.3,
// §13.4), a package variable (§26.3), the result of a subroutine (§13.4) or of
// another string method, and a property read after a task's timing control
// (§13.3). Each case here prints what the standard predicts and reads the
// simulator's output whole, so a method that answered "" or 0 for a receiver
// it did not recognise as a string fails on the value rather than on a
// diagnostic. A module-scope `string s` is the one receiver that always
// worked, so every case names its receiver some other way.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §6.16.1 and §6.16.4 on a property named through a handle, `h.s.len()`, and
// on the property's bare name inside a method of the class, `s.len()` in `l`.
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

// §8.11: `this.s` inside a method names the object's own property, and the
// method called on it answers for that property.
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

// The value-answering methods of §6.16.1 through §6.16.8 on one property:
// len, toupper, tolower chained on toupper's result, substr and getc.
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

// §6.16.9 and §6.16.10: the conversions read the property's text, so the
// number each answers is the one the text spells and not 0.
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

// §6.16.6: compare's argument is a property read through another handle, and
// its receiver a property through a handle; "abd" against "abc" is positive.
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

// §8.9 and §8.10: a static property named through the class scope resolution
// operator, `C::name.substr(0,0)`, and bare inside static methods of the
// class, `name.len()` and `name.toupper()`.
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

// §13.4 and §13.5.1: an input formal declared string holds the actual's text,
// and the methods called on it inside the body read that text.
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

// §13.3 and §13.5.1: an output formal declared string is a string the body
// writes and then reads through a method before it is copied out.
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

// §26.3: a package's string variable, read by its bare name under a wildcard
// import and through `P::ps`.
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

// §13.4 with §6.16: a method called on what a subroutine returned, and on what
// another string method returned, answers for that result. The module's own
// `s` is a different string from the property `get` returns and `l` reads
// (§23.9: the class scope is searched before the module's), so a reading of
// the bare name against the module's tables prints the wrong text or length.
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

// §8.6: a class's own methods are its own whatever they are named, so `len`
// and `substr` declared by the class run as the class's methods on a handle,
// on a property holding a handle and through the class scope; a dispatcher
// that took every call of a string method's name for one would answer the
// length of no string here.
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

// §13.4: a module function declared to return a string answers a string, so
// a method on its call reads the text it returned.
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

// §13.3 with §9.4: a task of the class suspends at `#5` and resumes on the
// same object, so a method on the property after the delay reads the text
// the statement before it wrote, and the assignment of a method's result
// back to the property stores that result.
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

// §8.3: a property of a class-typed property, `d.c.s`, is reached by a chain
// of handles, and the method answers for the string at its end.
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

}  // namespace
