#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(AssocArraySimulation, DynamicElementCreation) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 42;\n"
      "    result = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArraySimulation, MultipleElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa[2] = 20;\n"
      "    aa[3] = 30;\n"
      "    result = aa[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(AssocArraySimulation, OverwriteElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[7] = 100;\n"
      "    aa[7] = 200;\n"
      "    result = aa[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 200u);
}

TEST(AssocArraySimulation, NoStorageAllocatedUntilUsed) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial result = aa.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArraySimulation, RefArgAllocatesNonexistentEntry) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  task automatic inc_ref(ref int x);\n"
      "    x = x + 1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    inc_ref(aa[5]);\n"
      "    result = aa.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// §7.8 — the element data type may be any type allowed for a fixed-size array,
// not only a plain int. Drive a packed-vector element type end-to-end and read
// the stored value back to confirm the declared element type governs storage.
TEST(AssocArraySimulation, VectorElementStoredAndRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3] = 8'hAB;\n"
      "    result = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xABu);
}

// §7.8 — copying a whole associative array is one of the two exceptions to the
// "select an element first" rule. This drives the copy end-to-end (real
// declaration + whole-array assignment syntax) and confirms the destination
// receives the source's entries, not just that the copy elaborates.
TEST(AssocArraySimulation, WholeArrayCopyDuplicatesEntries) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int bb[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3] = 77;\n"
      "    bb = aa;\n"
      "    result = bb[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

// §9.4.2 has a non-edge implicit event "detected on any change in the value of
// the expression" and names an aggregate element as a lawful operand of one:
// "Object (class instance) members or aggregate elements can be any type as
// long as the result of the expression is a singular value". The clause puts
// the duty on the writer -- "Changing the value of object data members,
// aggregate elements ... shall cause the event expression to be reevaluated" --
// and an associative array's entries live outside the variable an @(aa[3]) arms
// its watcher on, so the write has to announce the change itself.
TEST(AssocArraySimulation, AssocElementWriteWakesAnEventControlOnThatElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  int woke;\n"
      "  always @(aa[3]) woke = woke + 1;\n"
      "  initial begin\n"
      "    woke = 0;\n"
      "    #1 aa[3] = 8'hF0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      "woke");
  EXPECT_EQ(v, 1u);
}

// The same event on the other writer: `aa[3][3:0]` is §7.8.7's write to bits of
// an element, which goes through TryWriteAssocElementBits rather than the
// whole-element store, so a notification placed on one does not reach the
// other. Two changes after the control armed, so the count discriminates
// between a fix that reached both writers and one that reached only the first.
TEST(AssocArraySimulation,
     AssocElementBitSelectWriteWakesAnEventControlOnThatElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  int woke;\n"
      "  always @(aa[3]) woke = woke + 1;\n"
      "  initial begin\n"
      "    woke = 0;\n"
      "    #1 aa[3] = 8'hF0;\n"
      "    #1 aa[3][3:0] = 4'hA;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      "woke");
  EXPECT_EQ(v, 2u);
}

// The other awaiter route onto the same notification: an inferred sensitivity
// list reduces a select read to its base name, so the always_comb arms an
// AnyChangeAwaiter on `aa` and resumes on the notification alone -- the
// comparison that awaiter makes is skipped for a name FindAssocArray answers,
// the array's own variable holding no element value to compare.
TEST(AssocArraySimulation, AssocElementWriteWakesAnAlwaysCombThatReadsIt) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  logic [7:0] b;\n"
      "  always_comb b = aa[3];\n"
      "  initial begin\n"
      "    #1 aa[3] = 8'hF0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(v, 0xF0u);
}

// §7.8's declaration is a declaration wherever it is written, and §6.21 puts a
// variable declared inside a subroutine among the ones a subroutine declares.
// SimContext::CreateAssocArray was reached from the lowering of a module's own
// variables and from an associative-array formal argument and from nowhere
// else, so an array declared among a subroutine's statements existed for no
// name: every index write stored nothing and every read answered the element
// type's default, with nothing reported (#3614).

// §7.8: "allocate storage for elements only when they are used". The write is
// what uses the element, and the read is what says the storage it allocated is
// the storage the key reaches.
TEST(AssocArraySimulation, ADeclarationInsideAFunctionBuildsTheArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function int keep();\n"
      "    int aa [int];\n"
      "    aa[7] = 42;\n"
      "    return aa[7];\n"
      "  endfunction\n"
      "  initial result = keep();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// §7.8.6's copy of a whole associative array between two of them declared the
// same way, which is the form #3496 could not write while this was open:
// TryAssocCopyAssign asks SimContext::FindAssocArray for both names and
// declined for both.
TEST(AssocArraySimulation, ACopyBetweenTwoDeclaredInsideAFunction) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function int copy();\n"
      "    int src [int];\n"
      "    int dst [int];\n"
      "    src[7] = 42;\n"
      "    dst = src;\n"
      "    return dst[7];\n"
      "  endfunction\n"
      "  initial result = copy();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// §7.8's index type decides which values are one element, so a `string` index
// is a different map from an integral one and the array a subroutine declares
// is keyed by the type its dimension names.
TEST(AssocArraySimulation, AStringKeyedArrayInsideAFunctionKeysByTheString) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function int keyed();\n"
      "    int aa [string];\n"
      "    aa[\"seven\"] = 42;\n"
      "    return aa[\"seven\"];\n"
      "  endfunction\n"
      "  initial result = keyed();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// The same declaration among a module's items, which is the path
// Lowerer::LowerVar serves. Without it a fix that moved the creation rather
// than adding one would pass the three above and take this away.
TEST(AssocArraySimulation, TheSameDeclarationAmongAModulesItemsStillBuildsOne) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa [int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[7] = 42;\n"
      "    result = aa[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// §7.8 lets the element type be any type a fixed-size array may have, and
// §8.4 has `new` construct an object whose handle the element then holds, so
// `m["a"].v` is the property of the object constructed under "a". The second
// entry holds a different value, so a read that reached the last object
// constructed rather than the one under the key would answer 6.
TEST(AssocArraySimulation,
     AMemberSelectedOnAnElementOfADeclaredArrayOfHandlesReadsItsObject) {
  auto v = RunAndGet(
      "class C;\n"
      "  int v;\n"
      "  function new(int x); v = x; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C m[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    m[\"a\"] = new(5);\n"
      "    m[\"b\"] = new(6);\n"
      "    result = m[\"a\"].v;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

// The same element with a method selected on it: the method runs on the
// object under the key, reading its own property. An answer of 8 would be the
// other object's; 0 is no object at all.
TEST(AssocArraySimulation,
     AMethodCalledOnAnElementOfADeclaredArrayOfHandlesRunsOnItsObject) {
  auto v = RunAndGet(
      "class C;\n"
      "  int v;\n"
      "  function new(int x); v = x; endfunction\n"
      "  function int m(); return v + 1; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C m[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    m[\"a\"] = new(5);\n"
      "    m[\"b\"] = new(7);\n"
      "    result = m[\"a\"].m();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 6u);
}

// An integral index keys the same way (§7.8.1): the property of the object
// under 3 and the method of the one under 4, 70 + 10.
TEST(AssocArraySimulation,
     AnIntKeyedArrayOfHandlesReachesTheObjectUnderEachKey) {
  auto v = RunAndGet(
      "class C;\n"
      "  int v;\n"
      "  function new(int x); v = x; endfunction\n"
      "  function int m(); return v + 1; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C q[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q[3] = new(7);\n"
      "    q[4] = new(9);\n"
      "    result = q[3].v * 10 + q[4].m();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 80u);
}

// §7.8 in an instantiated module: `int aa[int]` declared in M, which top
// instantiates as `m`, is stored under "m.aa", and §23.9 resolves the bare
// name `aa` inside M through the instance. SimContext::FindAssocArray asked
// for the bare key alone, so no associative array answered inside the
// instance: the element write and read fell to the carrier variable the
// lowerer creates under the name, and num() was asked of no array. Two
// entries allocated by assignment (§7.8) read back 17 under 9 and a count of
// 2.
TEST(AssocArraySimulation, ChildInstanceIntKeyedArrayHoldsItsElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  int aa[int];\n"
      "  int r;\n"
      "  initial begin\n"
      "    aa[5] = 42;\n"
      "    aa[9] = 17;\n"
      "    r = aa[9] * 100 + aa.num();\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("m.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1702u);
}

// A string index keys the same lookup (§7.8), and foreach walks the entries
// the array holds (§12.7.3): three written in the instance sum to 3 + 4 + 5,
// with size() answering 3. With no array found by the bare name, the loop
// ran over the carrier variable instead and the sum stayed at 0.
TEST(AssocArraySimulation, ChildInstanceStringKeyedArrayHoldsItsElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  int sa[string];\n"
      "  int r, s;\n"
      "  initial begin\n"
      "    s = 0;\n"
      "    sa[\"k\"] = 3;\n"
      "    sa[\"j\"] = 4;\n"
      "    sa[\"l\"] = 5;\n"
      "    foreach (sa[key]) s = s + sa[key];\n"
      "    r = sa.size() * 100 + s;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("m.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 312u);
}

// §7.8 (printed page 163 of the LRM) with §8.5: a class property may be an
// associative array of any element type, and §8.4 (printed 181) makes an
// element declared with a class's name a handle, constructed by `new` into
// the entry and read through it as a declared array's is above. The two
// tests below share the classes and read 5, the constructor's argument, from
// the module through a handle and from a method by the bare name. Before
// this only a declared array had the two paths (HandleArrayOfSelect in
// eval_assoc_class_handles.cpp asked for a bare declared name alone), so
// `x.m["a"] = new(5)` constructed nothing and `x.m["a"].v` read 0.
static std::string AssocPropertyDesign(std::string_view rest) {
  return "class C;\n"
         "  int v;\n"
         "  function new(int x); v = x; endfunction\n"
         "endclass\n"
         "class H;\n"
         "  C m[string];\n"
         "  function int go();\n"
         "    m[\"b\"] = new(5);\n"
         "    return m[\"b\"].v;\n"
         "  endfunction\n"
         "endclass\n" +
         std::string(rest);
}

TEST(AssocArraySimulation, AssocPropertyOfHandlesConstructedThroughAHandle) {
  EXPECT_EQ(RunAndGet(AssocPropertyDesign("module t;\n"
                                          "  H x = new;\n"
                                          "  int result;\n"
                                          "  initial begin\n"
                                          "    x.m[\"a\"] = new(5);\n"
                                          "    result = x.m[\"a\"].v;\n"
                                          "  end\n"
                                          "endmodule\n"),
                      "result"),
            5u);
}

TEST(AssocArraySimulation, AssocPropertyOfHandlesConstructedInAMethod) {
  EXPECT_EQ(RunAndGet(AssocPropertyDesign("module t;\n"
                                          "  H x = new;\n"
                                          "  int result;\n"
                                          "  initial result = x.go();\n"
                                          "endmodule\n"),
                      "result"),
            5u);
}

// §7.4.4 (printed page 155) with §6.18: an array's unpacked dimensions may be
// defined in stages with typedef, so `ie_t x;` under `typedef bit ie_t[int];`
// declares an associative array indexed by int (§7.8), as `bit x[int]` does.
// The dimensions of an associative typedef were the one form the elaborator
// did not carry to a declaration through the name, so the module variable was
// a single bit and `x[5] = 1` was reported as a bit-select of a scalar.
TEST(AssocArraySimulation, ModuleVariableThroughAnAssocTypedefIsAnAssocArray) {
  SimFixture f;
  auto out = RunCapture(
      "typedef bit ie_t[int];\n"
      "module t;\n"
      "  ie_t x;\n"
      "  initial begin\n"
      "    x[5] = 1;\n"
      "    x[9] = 1;\n"
      "    $display(\"num=%0d\", x.num());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "num=2\n");
}

// §7.4.4 as above, for a local of a module's procedure, which the elaborator
// rewrites through the same record of the typedef's dimensions.
TEST(AssocArraySimulation, ProceduralLocalThroughAnAssocTypedefIsAnAssocArray) {
  SimFixture f;
  auto out = RunCapture(
      "typedef bit ie_t[int];\n"
      "module t;\n"
      "  initial begin\n"
      "    ie_t y;\n"
      "    y[2] = 1;\n"
      "    y[7] = 1;\n"
      "    y[11] = 1;\n"
      "    $display(\"num=%0d\", y.num());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "num=3\n");
}

// §7.4.4 as above, for a local of a class method through a typedef declared
// outside any class: the local's type is the one the name stands for wherever
// it was declared (§6.18), so `ue_t u;` is an associative array. The method's
// local looked the name up among the class's own typedefs alone, found none,
// and was a scalar the keyed writes never reached.
TEST(AssocArraySimulation, MethodLocalThroughAUnitAssocTypedefIsAnAssocArray) {
  SimFixture f;
  auto out = RunCapture(
      "typedef bit ue_t[int];\n"
      "class K;\n"
      "  function int f();\n"
      "    ue_t u;\n"
      "    u[3] = 1;\n"
      "    u[4] = 1;\n"
      "    return u.num();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin static K k = new; $display(\"num=%0d\", k.f()); end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "num=2\n");
}

// §7.8 with §7.4: an associative array whose element type is an associative
// array keeps an inner array under each outer key. A write with two indices
// allocates the entry at both levels (§7.8.7), and num(), exists() and an
// element select on `m["a"]` answer for that key's inner array alone.
TEST(AssocArraySimulation, AssocOfAssocKeepsAnInnerArrayPerKey) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int m[string][int];\n"
      "  initial begin\n"
      "    m[\"a\"][1] = 41; m[\"a\"][2] = 42; m[\"b\"][9] = 9;\n"
      "    $display(\"%0d %0d %0d %0d\", m.num(), m[\"a\"].num(), "
      "m[\"b\"].num(),\n"
      "             m[\"a\"][2]);\n"
      "    $display(\"%0d %0d %0d\", m[\"a\"].exists(2), m[\"b\"].exists(2),\n"
      "             m[\"b\"][9]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 2 1 42\n1 0 9\n");
}

// §7.8 with §6.11: an element of an associative array is a variable of the
// element type, so it reads with that type's signedness whatever the value
// written into it was: the unsigned 32'hFFFFFFFD in an `int` element is -3,
// less than 0, and the signed -3 in a `bit [31:0]` element is 4294967293. An
// array declared in a procedural block, one with a string index and the inner
// array of an associative array of associative arrays read alike.
TEST(AssocArraySimulation, AnElementReadsWithTheElementTypesSignedness) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int aa[int];\n"
      "  int as[string];\n"
      "  bit [31:0] ua[int];\n"
      "  int mm[string][int];\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    int ba[int];\n"
      "    bit [31:0] bu[int];\n"
      "    u = 32'hFFFFFFFD;\n"
      "    aa[0] = u; as[\"k\"] = u; ua[0] = -3; mm[\"k\"][0] = u;\n"
      "    ba[0] = u; bu[0] = -3;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", aa[0] < 0, as[\"k\"] < 0,\n"
      "             ua[0] < 0, mm[\"k\"][0] < 0, ba[0] < 0, bu[0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 0 1 1 0\n");
}

// §7.8 with §6.16 and §6.12: the element type's signedness is an integral
// type's alone, so an element of a string or a real type, written from a
// variable of its type, reads back as the string and the real it holds.
TEST(AssocArraySimulation, AStringOrRealElementReadsAsItsOwnType) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  string sa[int];\n"
      "  real ra[string];\n"
      "  string s = \"hey\";\n"
      "  real r = -1.25;\n"
      "  initial begin\n"
      "    sa[1] = s; ra[\"k\"] = r;\n"
      "    $display(\"%s %0.2f %0d\", sa[1], ra[\"k\"], ra[\"k\"] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hey -1.25 1\n");
}

// §7.8 with §6.16: an element of an associative array of strings is a string,
// so the string methods answer from the text it holds, for an array a module,
// a block or an imported package declares, under an integral or a string
// index.
TEST(AssocArraySimulation, AStringMethodReadsTheElementsText) {
  SimFixture f;
  auto out = RunCapture(
      "package p;\n"
      "  string ps[int];\n"
      "endpackage\n"
      "module t;\n"
      "  import p::*;\n"
      "  string sa[int];\n"
      "  string sk[string];\n"
      "  initial begin\n"
      "    string sb[byte];\n"
      "    sa[1] = \"hi\"; sk[\"k\"] = \"wxyz\"; sb[2] = \"abc\";\n"
      "    ps[0] = \"pqrst\";\n"
      "    $display(\"%0d %0d %0d %0d\", sa[1].len(), sk[\"k\"].len(),\n"
      "             sb[2].len(), ps[0].len());\n"
      "    $display(\"%s %s %0d\", sa[1].toupper(), sk[\"k\"].substr(1, 2),\n"
      "             sb[2].getc(1));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 4 3 5\nHI xy 98\n");
}

// §7.8 with §6.11 and §26.2: an associative array a package declares has
// elements of its own element type too.
TEST(AssocArraySimulation, AnElementOfAPackageAssociativeArrayReadsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "package p;\n"
      "  int aa[int];\n"
      "endpackage\n"
      "module t;\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    u = 32'hFFFFFFFD;\n"
      "    p::aa[0] = u;\n"
      "    $display(\"%0d\", p::aa[0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

// §7.8 with §6.11 and §13.5: an associative array formal, `int a[int]`, has
// elements of its own element type, so the unsigned value the actual's entry
// was written with reads in the body as a signed int, less than 0.
TEST(AssocArraySimulation, AnElementOfAnAssociativeArrayFormalReadsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int x[int];\n"
      "  bit [31:0] u;\n"
      "  function int negative(int a[int]);\n"
      "    return a[0] < 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    u = 32'hFFFFFFFD;\n"
      "    x[0] = u;\n"
      "    $display(\"%0d\", negative(x));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

// §7.8 with §6.11, §8.5 and §8.12: an associative array property has elements
// of its declared element type, and so does the array a shallow copy of the
// object gives the copy.
TEST(AssocArraySimulation, AnElementOfAnAssociativeArrayPropertyReadsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    int m[int];\n"
      "  endclass\n"
      "  C c, d;\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    u = 32'hFFFFFFFD;\n"
      "    c = new;\n"
      "    c.m[0] = u;\n"
      "    d = new c;\n"
      "    $display(\"%0d %0d\", c.m[0] < 0, d.m[0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

}  // namespace
