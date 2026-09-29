#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

namespace {

// §8.5 puts no restriction on a property's data type, and §7.2 declares a
// structure whose members are selected by name. A property declared with an
// unpacked struct typedef holds the structure as one value the width of the
// typedef's layout, so a member written through the handle lands in that
// member's bits and a member read through the handle comes out of them. The
// first member sits above the second in the layout, so losing it to a value
// narrower than the layout reads 12 rather than 312.
TEST(ObjectPropertySim,
     UnpackedStructPropertyMembersWrittenAndReadThroughAHandle) {
  EXPECT_EQ(RunAndGet("typedef struct { int f; int g; } pair_t;\n"
                      "class C;\n"
                      "  pair_t p;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.p.f = 3;\n"
                      "    c.p.g = 12;\n"
                      "    out = c.p.f * 100 + c.p.g;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            312u);
}

// §8.11 lets a method name its object's property bare, so `p.f = x` inside a
// method writes the member of the structure the running object's `p` holds,
// and `p.f * 100 + p.g` reads both members back out of it. Dropping the write
// or reading the member as an undeclared name answers 0.
TEST(ObjectPropertySim, UnpackedStructPropertyMembersWrittenAndReadInMethods) {
  EXPECT_EQ(RunAndGet("typedef struct { int f; int g; } pair_t;\n"
                      "class C;\n"
                      "  pair_t p;\n"
                      "  function void setf(int x); p.f = x; endfunction\n"
                      "  function void setg(int x); p.g = x; endfunction\n"
                      "  function int sum(); return p.f * 100 + p.g; "
                      "endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.setf(7);\n"
                      "    c.setg(25);\n"
                      "    out = c.sum();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            725u);
}

// The two routes reach the same structure: a member written through the
// handle is read by a method, and a member written by a method is read
// through the handle. 3 from `c.p.f`, 12 from `c.p.g` and 15 from the method's
// sum make 3135; a member lost on either route changes each digit group.
TEST(ObjectPropertySim,
     UnpackedStructPropertyMemberWrittenThroughAHandleReadInAMethod) {
  EXPECT_EQ(RunAndGet("typedef struct { int f; int g; } pair_t;\n"
                      "class C;\n"
                      "  pair_t p;\n"
                      "  function int sum(); return p.f + p.g; endfunction\n"
                      "  function void setg(int x); p.g = x; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.p.f = 3;\n"
                      "    c.setg(12);\n"
                      "    out = c.p.f * 1000 + c.p.g * 10 + c.sum();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            3135u);
}

// §8.5 puts no restriction on a property's data type and §26.3 references a
// package's declarations through the package scope resolution operator
// (printed pages 183 and 808 of IEEE 1800-2023), so `pk::sev_t s =
// pk::MED;` declares a property of the package's enum type holding the
// package's MED. The declaration was a parse error at the `::`. MED is 2 and
// HIGH 3, so the initializer read through the handle and the value written
// through it after make 23; a lost initializer reads 3 and a lost write 20.
TEST(ObjectPropertySim, PackageScopedEnumPropertyHoldsItsInitializer) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  typedef enum {LOW, MED = 2, HIGH} sev_t;\n"
                      "endpackage\n"
                      "class C;\n"
                      "  pk::sev_t s = pk::MED;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    out = c.s * 10;\n"
                      "    c.s = pk::HIGH;\n"
                      "    out = out + c.s;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            23u);
}

// A.2.7 gives a method's return type the same data_type, so a method returns
// `pk::sev_t` as a property is declared with it. `cur` returns the property
// as initialized (2), `top` writes HIGH into it and returns it (3), and `cur`
// then returns the written value (3): 233. A return type read as the method's
// class name leaves no method to call.
TEST(ObjectPropertySim, PackageScopedEnumReturnedByAMethod) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  typedef enum {LOW, MED = 2, HIGH} sev_t;\n"
                      "endpackage\n"
                      "class C;\n"
                      "  pk::sev_t s = pk::MED;\n"
                      "  function pk::sev_t cur(); return s; endfunction\n"
                      "  function pk::sev_t top();\n"
                      "    s = pk::HIGH;\n"
                      "    return s;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    out = c.cur() * 100;\n"
                      "    out = out + c.top() * 10;\n"
                      "    out = out + c.cur();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            233u);
}

// §8.5 with §7.2 and §7.4.2: an unpacked array member of a structure a
// property holds is an array of elements, each written and read on its own --
// bare in a method, through `this` and through a handle -- so data[2], data[0]
// and data[1] keep 9, 4 and 7. Taken as a bit-select of the member's value,
// every element read 0.
TEST(ObjectPropertySim, ElementsOfAStructPropertysArrayMember) {
  const char* src =
      "module t;\n"
      "  typedef struct { int a; byte data[3]; } pkt_t;\n"
      "  class C;\n"
      "    pkt_t s;\n"
      "    function void fill(); s.data[2] = 9; s.data[0] = 4; endfunction\n"
      "    function int get(); return s.data[2]; endfunction\n"
      "    function int get_this(); return this.s.data[0]; endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  int d2, d0, d1, g, gt;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.fill();\n"
      "    h.s.data[1] = 7;\n"
      "    d2 = h.s.data[2];\n"
      "    d0 = h.s.data[0];\n"
      "    d1 = h.s.data[1];\n"
      "    g = h.get();\n"
      "    gt = h.get_this();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "d2"), 9u);
  EXPECT_EQ(RunAndGet(src, "d0"), 4u);
  EXPECT_EQ(RunAndGet(src, "d1"), 7u);
  EXPECT_EQ(RunAndGet(src, "g"), 9u);
  EXPECT_EQ(RunAndGet(src, "gt"), 4u);
}

// §8.5 with §7.5 and §7.2: a dynamic array property of structures is sized
// and its elements' members written in a method, and read through the handle
// -- `d = new[2]; d[1].a = 11;` -- even where the module declaring the class
// has a variable `d` of its own, which §8.11 and §23.9 put behind the
// property inside a method. The module's `d` took the new[] and the member.
TEST(ObjectPropertySim, DynamicArrayPropertyOfStructsInAMethod) {
  const char* src =
      "module t;\n"
      "  typedef struct { int a; int b; } s_t;\n"
      "  class C;\n"
      "    s_t d[];\n"
      "    function void fill(); d = new[2]; d[1].a = 11; endfunction\n"
      "  endclass\n"
      "  s_t d[];\n"
      "  C h;\n"
      "  int n, a1, md;\n"
      "  initial begin\n"
      "    d = new[3];\n"
      "    h = new;\n"
      "    h.fill();\n"
      "    n = h.d.size();\n"
      "    a1 = h.d[1].a;\n"
      "    md = d.size();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "n"), 2u);
  EXPECT_EQ(RunAndGet(src, "a1"), 11u);
  EXPECT_EQ(RunAndGet(src, "md"), 3u);
}

// §8.5 with §7.8 and §7.2: an associative array property of structures has
// an element's members written in a method and through the handle, which
// creates the entry its key names, and read back through the handle: `a` holds
// 3 and 4, `b` 9, and the array two entries. Each member write went nowhere.
TEST(ObjectPropertySim, AssociativeArrayPropertyOfStructMemberWrites) {
  const char* src =
      "module t;\n"
      "  typedef struct { int x; int y; } pt_t;\n"
      "  class C;\n"
      "    pt_t m[string];\n"
      "    function void fill(); m[\"a\"].x = 3; m[\"a\"].y = 4; "
      "endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  int ax, ay, bx, n;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.fill();\n"
      "    h.m[\"b\"].x = 9;\n"
      "    ax = h.m[\"a\"].x;\n"
      "    ay = h.m[\"a\"].y;\n"
      "    bx = h.m[\"b\"].x;\n"
      "    n = h.m.num();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ax"), 3u);
  EXPECT_EQ(RunAndGet(src, "ay"), 4u);
  EXPECT_EQ(RunAndGet(src, "bx"), 9u);
  EXPECT_EQ(RunAndGet(src, "n"), 2u);
}

// §8.7 with §10.9.1: an array assignment pattern initializing a fixed-size
// array property gives each element the item at its position, where the
// pattern evaluated as one value gave every element the last item.
TEST(ObjectPropertySim, PatternInitializerOfArrayPropertyFillsEachElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    int f[4] = '{5, 1, 8, 3};\n"
      "  endclass\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    result = h.f[0] * 1000 + h.f[1] * 100 + h.f[2] * 10 + h.f[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5183u);
}

// §8.11 with §10.9.1: a pattern assigned to an array property by its bare name
// in a method is stored element by element on the object.
TEST(ObjectPropertySim, PatternAssignedToArrayPropertyInAMethodIsStored) {
  auto v = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    int a[3];\n"
      "    function new(); a = '{1, 2, 3}; endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    result = h.a[0] * 100 + h.a[1] * 10 + h.a[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 123u);
}

// §8.5 with §10.9.1: through a handle, an index key, `default` and a
// replication each place their items into the array property.
TEST(ObjectPropertySim, KeyedAndReplicatedPatternsIntoArrayPropertyViaHandle) {
  auto v = RunAndGet(
      "module t;\n"
      "  class C; int a[3]; int r[3]; endclass\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.a = '{1:9, default:1};\n"
      "    h.r = '{3{3}};\n"
      "    result = (h.a[0] * 100 + h.a[1] * 10 + h.a[2]) * 10 + h.r[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1913u);
}

// §8.5 with §10.9.2: `'{default:8}` into a structure property through a handle
// fills every member by the property's layout, where evaluated as one 32-bit
// value it set the last member alone.
TEST(ObjectPropertySim, DefaultPatternIntoStructPropertyViaHandleFillsAll) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x; int y; } st;\n"
      "  class C; st s; endclass\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.s = '{default:8};\n"
      "    result = h.s.x * 10 + h.s.y;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 88u);
}

// §8.11 with §10.9.2: the same by the property's bare name in a method, with a
// member key beside the default.
TEST(ObjectPropertySim, KeyedPatternIntoStructPropertyInAMethodFillsAll) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int x; int y; } st;\n"
      "  class C;\n"
      "    st s;\n"
      "    function void f(); s = '{x:6, default:1}; endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.f();\n"
      "    result = h.s.x * 10 + h.s.y;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 61u);
}

// §8.5 with §8.15: `h.d.k = 64` writes the property of the object `h.d` refers
// to as its declared class Inner holds it, so a method of Inner called
// through the chain and a handle of type Inner both read 64.
TEST(ObjectPropertySim, WriteThroughChainedHandleIsTheObjectsProperty) {
  auto v = RunAndGet(
      "module t;\n"
      "  class Inner;\n"
      "    int k;\n"
      "    function int getk(); return k; endfunction\n"
      "  endclass\n"
      "  class Holder; Inner d; endclass\n"
      "  Holder h; Inner i;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new; h.d = new;\n"
      "    h.d.k = 64;\n"
      "    i = h.d;\n"
      "    result = h.d.getk() * 1000 + i.k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 64064u);
}

// §8.5 with §7.4, §7.5 and §8.9: an element of a property that is an array of
// strings -- fixed-size, static or dynamic -- holds the string written to it
// through a handle or the class scope, as it does when a method writes it, and
// the string methods read it. Taken for one string, the property's select was
// a character write into its empty text, so the element read back empty.
TEST(ObjectPropertySim, StringArrayPropertyElementsWrittenFromOutside) {
  auto v = RunAndGet(
      "class C;\n"
      "  string inst[2];\n"
      "  static string names[2];\n"
      "  string sd[];\n"
      "  function void set(); inst[0] = \"in\"; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new; h.set();\n"
      "    h.inst[1] = \"ab\"; C::names[0] = \"s\";\n"
      "    h.sd = new[1]; h.sd[0] = \"dy\";\n"
      "    result = (h.inst[0] == \"in\") + 10 * (h.inst[1] == \"ab\") +\n"
      "             100 * (C::names[0] == \"s\") + 1000 * (h.sd[0] == \"dy\") "
      "+\n"
      "             10000 * h.inst[1].len();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 21111u);
}

// §8.5 lets a property be of a structure type, and §21.2.1.6 has %p print an
// aggregate as an assignment pattern of its members wherever the argument
// names one, a property named bare in a method or through a handle alike.
// The property is no variable, so no layout was found for it and it printed
// as the one number its bits make, 12884901893.
TEST(ObjectPropertySim, StructurePropertyPrintsAsPatternWithP) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int a; int b; } GS;\n"
                       "class Box;\n"
                       "  GS s;\n"
                       "  function void set(); s.b = 5; s.a = 3; endfunction\n"
                       "  function void show(); $display(\"m=%p\", s); "
                       "endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Box b;\n"
                       "  initial begin\n"
                       "    b = new; b.set(); b.show();\n"
                       "    $display(\"h=%p\", b.s);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "m='{a:3, b:5}\nh='{a:3, b:5}\n");
}

// The tagged union a property's type names in the tests below: §8.5 lets a
// property be of it, and §7.3.2 has the value the property holds carry its tag
// beside the member, whichever object holds it and however it is named.
constexpr const char* kOptBox =
    "typedef union tagged { void None; int Some; } Opt;\n"
    "class Box;\n"
    "  Opt o;\n"
    "  function void set(int v); o = tagged Some (v); endfunction\n"
    "  function void clear(); o = tagged None; endfunction\n"
    "  function string describe();\n"
    "    case (o) matches\n"
    "      tagged Some .v : return $sformatf(\"some %0d\", v);\n"
    "      tagged None : return \"none\";\n"
    "    endcase\n"
    "    return \"?\";\n"
    "  endfunction\n"
    "  function void show(); $display(\"%p\", o); endfunction\n"
    "  function int bad(); return o.None; endfunction\n"
    "endclass\n";

// §21.2.1.6 prints a tagged union as its tag and the member the tag names, so
// the property prints '{Some:9} in a method and through a handle, and each of
// two objects prints its own tag. Carrying no tag, the property printed 9.
TEST(ObjectPropertySim, TaggedUnionPropertyPrintsItsTagWithP) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kOptBox) +
                           "module t;\n"
                           "  Box b, c;\n"
                           "  initial begin\n"
                           "    b = new; c = new; b.set(9); c.set(4);\n"
                           "    b.show(); $display(\"%p\", c.o);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "'{Some:9}\n'{Some:4}\n");
}

// §8.12 copies every property of an object into its shallow copy, and the
// value a tagged-union property holds carries its tag (§7.3.2), so the copy's
// property prints with the same tag, and each object's tag is its own after.
TEST(ObjectPropertySim, ShallowCopyKeepsTaggedUnionPropertyTag) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(std::string(kOptBox) + "module t;\n"
                                        "  Box b, c;\n"
                                        "  initial begin\n"
                                        "    b = new; b.set(9);\n"
                                        "    c = new b;\n"
                                        "    $display(\"%p %p\", b.o, c.o);\n"
                                        "    c.clear();\n"
                                        "    $display(\"%s %s\", b.describe(), "
                                        "c.describe());\n"
                                        "  end\n"
                                        "endmodule\n",
                 f),
      "'{Some:9} '{Some:9}\nsome 9 none\n");
}

// §12.6 matches `tagged Some .v` against the tag the property holds, binding v
// to its member, and `tagged None` against the void member's tag, so the case
// in the method selects by what was last assigned. With no tag carried, neither
// pattern matched and the method fell through to "?".
TEST(ObjectPropertySim, TaggedUnionPropertyMatchesItsTagInMethod) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kOptBox) +
                           "module t;\n"
                           "  Box b;\n"
                           "  initial begin\n"
                           "    b = new; b.set(9); $display(\"%s\", "
                           "b.describe());\n"
                           "    b.clear(); $display(\"%s\", b.describe());\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "some 9\nnone\n");
}

// §11.9 makes a read of a tagged union through a member other than the one
// its tag names a run-time error, a property's as a variable's: `o.None` in a
// method after `o = tagged Some (9)`. It read 0 and reported nothing.
TEST(ObjectPropertySim, TaggedUnionPropertyMismatchedReadIsReported) {
  SimFixture f;
  RunCapture(std::string(kOptBox) +
                 "module t;\n"
                 "  Box b;\n"
                 "  int r;\n"
                 "  initial begin b = new; b.set(9); r = b.bad(); end\n"
                 "endmodule\n",
             f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member 'None' of "
                            "tagged union 'o' which currently has tag 'Some'",
                            14, "11.9"));
}

}  // namespace
