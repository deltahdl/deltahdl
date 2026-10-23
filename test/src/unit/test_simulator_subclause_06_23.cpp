#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.23 — type(this) represents the type of the enclosing class. Inside a
// method of class C, comparing type(this) against type(C) matches, so the
// method takes the true branch. The class and the call are built from real
// source syntax and driven through the full pipeline; the returned value is
// observed at run time.
TEST(TypeOfThisSim, MatchesEnclosingClass) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  function int check();\n"
                      "    int r;\n"
                      "    if (type(this) == type(C)) r = 1;\n"
                      "    else r = 2;\n"
                      "    return r;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.check();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.23 — type(this) is the enclosing class, so it does not match a different
// class. Comparing type(this) in C against type(D) is false; the else branch
// runs.
TEST(TypeOfThisSim, DiffersFromOtherClass) {
  EXPECT_EQ(RunAndGet("class D;\n"
                      "endclass\n"
                      "class C;\n"
                      "  function int check();\n"
                      "    int r;\n"
                      "    if (type(this) == type(D)) r = 1;\n"
                      "    else r = 2;\n"
                      "    return r;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.check();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            2u);
}

// §6.23 — a class type reference never matches a built-in type reference, so
// type(this) compared against type(int) is false.
TEST(TypeOfThisSim, DiffersFromBuiltinType) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  function int check();\n"
                      "    int r;\n"
                      "    if (type(this) == type(int)) r = 1;\n"
                      "    else r = 2;\n"
                      "    return r;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.check();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            2u);
}

// §6.23 — the inequality form negates the match, so type(this) != type(int) is
// true inside a class method.
TEST(TypeOfThisSim, InequalityWithBuiltinIsTrue) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  function int check();\n"
                      "    int r;\n"
                      "    if (type(this) != type(int)) r = 1;\n"
                      "    else r = 2;\n"
                      "    return r;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.check();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.23/§8.11 — type(this) resolves to the enclosing class even in a static
// method, where there is no instance handle: the class is the one whose method
// body is executing. A static check() compares type(this) against type(C) and
// matches.
TEST(TypeOfThisSim, MatchesEnclosingClassInStaticMethod) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static function int check();\n"
                      "    int r;\n"
                      "    if (type(this) == type(C)) r = 1;\n"
                      "    else r = 2;\n"
                      "    return r;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = C::check();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §6.23 with A.2.8: `var type(a) v;` among a block's items declares v with the
// self-determined type of `a`, so v is the 32-bit signed int of `int a` and
// holds -7, which a one-bit v would read as 1.
TEST(TypeOfExprBlockVarSim, TakesTheIntTypeOfAModuleVariable) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int a = 3;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    var automatic type(a) v = -7;\n"
                      "    r = v;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xFFFFFFF9u);
}

// §6.23: the type of `w`, `logic [11:0]`, gives x twelve bits, so all twelve
// written ones survive and $bits(x) is 12.
TEST(TypeOfExprBlockVarSim, TakesTheVectorTypeOfAModuleVariable) {
  const std::string kSrc =
      "module t;\n"
      "  logic [11:0] w;\n"
      "  int r, b;\n"
      "  initial begin\n"
      "    var type(w) x;\n"
      "    x = 12'hFFF;\n"
      "    r = x;\n"
      "    b = $bits(x);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 4095u);
  EXPECT_EQ(RunAndGet(kSrc, "b"), 12u);
}

// §6.23 takes the type of the expression with the names in scope at the
// declaration, so the block's own `shortint a` hides the module's 4-bit `a`:
// z is 16 bits wide and signed, and holds -2.
TEST(TypeOfExprBlockVarSim, TakesTheTypeOfAnEarlierBlockLocal) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] a;\n"
      "  int r, b;\n"
      "  initial begin\n"
      "    shortint a;\n"
      "    var automatic type(a) z = -2;\n"
      "    r = z;\n"
      "    b = $bits(z);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0xFFFFFFFEu);
  EXPECT_EQ(RunAndGet(kSrc, "b"), 16u);
}

// §6.23 with §6.24.1: a type reference is a casting type, so `type(n)'(v)`
// with `bit [3:0] n` keeps the low four bits of 16'hABCF, 15; `type(s)'`
// with `byte s` makes 16'h00F0 the signed -16; and `type(bit [11:0])'` keeps
// twelve bits, 12'hBCF.
TEST(TypeOfExprCastSim, CastToATypeReferenceTakesTheReferencedType) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  byte s;\n"
      "  logic [15:0] v = 16'hABCF;\n"
      "  int d, e, g;\n"
      "  initial begin\n"
      "    d = type(n)'(v);\n"
      "    e = type(s)'(16'h00F0);\n"
      "    g = type(bit [11:0])'(v);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 15u);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0xFFFFFFF0u);
  EXPECT_EQ(RunAndGet(kSrc, "g"), 0xBCFu);
}

// §6.23 with §8.11: `var static type(this) m_inst;` in a static method is a
// handle of the method's class, so the singleton get() stores the object new()
// makes and hands the same one back on the next call, with its val of 9.
TEST(TypeOfExprCastSim, TypeOfThisMethodLocalIsAHandleOfTheClass) {
  const std::string kSrc =
      "module t;\n"
      "  class registry;\n"
      "    int val = 9;\n"
      "    static function registry get();\n"
      "      var static type(this) m_inst;\n"
      "      if (m_inst == null) m_inst = new();\n"
      "      return m_inst;\n"
      "    endfunction\n"
      "  endclass\n"
      "  registry r, r2;\n"
      "  int got, same, v;\n"
      "  initial begin\n"
      "    r = registry::get();\n"
      "    r2 = registry::get();\n"
      "    got = r != null;\n"
      "    same = r == r2;\n"
      "    v = r.val;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "got"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "same"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "v"), 9u);
}

// §6.23 with §6.22.1: a type-reference comparison in a procedure is true
// exactly when the types match -- a typedef renaming a built-in, a typedef of
// that typedef, `bit signed [7:0]` against byte (§6.22.1(e)), `byte signed`
// against byte, and two unpacked arrays of matching elements and bounds all
// match; `bit signed [0:7]` does not match byte, its range not being [7:0].
// Compared by name alone, every pair was 0.
TEST(TypeOfExprCastSim, TypeReferenceEqualityMatchesTypesInAProcedure) {
  const std::string kSrc =
      "module t;\n"
      "  typedef bit node;\n"
      "  typedef node type2;\n"
      "  typedef bit signed [7:0] BYTE;\n"
      "  typedef byte signed MY_CHAR;\n"
      "  typedef byte MEM_BYTES [256];\n"
      "  typedef bit signed [7:0] MY_MEM_BYTES [256];\n"
      "  typedef bit signed [0:7] ETYB;\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = {type(node) == type(bit), type(type2) == type(node),\n"
      "         type(BYTE) == type(byte), type(MY_CHAR) == type(byte),\n"
      "         type(MEM_BYTES) == type(MY_MEM_BYTES),\n"
      "         type(ETYB) == type(byte)};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b111110u);
}

// §6.23 with §26.2 and §3.12.1: a typedef or nettype of a package or of the
// compilation unit may name its type by a type reference to a value, or a
// typedef, its scope declares. a and b are the package's int, so -5 stands
// whole in each; c is the unit's four bits, so 5'h1F keeps 15; and n, of the
// unit's nettype, carries 4'hA. Left unresolved, each type was implicit, the
// mark of a forward typedef, and one bit wide.
TEST(TypeReferenceScopeSim, PackageAndUnitTypedefsOfATypeReference) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  int x;\n"
      "  typedef int base_t;\n"
      "  typedef type(x) xt;\n"
      "  typedef type(base_t) bt;\n"
      "endpackage\n"
      "logic [3:0] uy;\n"
      "typedef type(uy) ut;\n"
      "nettype type(uy) unt;\n"
      "module t;\n"
      "  p::xt a;\n"
      "  p::bt b;\n"
      "  ut c;\n"
      "  unt n;\n"
      "  assign n = 4'hA;\n"
      "  initial begin\n"
      "    a = -5;\n"
      "    b = -5;\n"
      "    c = 5'h1F;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"a", 0xFFFFFFFBu}, {"b", 0xFFFFFFFBu}, {"c", 0xFu}, {"n", 0xAu}});
}

// §6.23 with §8.5 and §23.9: a class property's type reference to a name its
// class does not declare reaches the scope around the class. w is the
// module's int x and u its four-bit parameter P, so -5 stands whole in w and
// 5'h1F keeps 15 in u, where a one-bit property held 1.
TEST(TypeReferenceScopeSim, ModuleClassPropertiesOfTheModulesNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  parameter logic [3:0] P = 1;\n"
      "  class C;\n"
      "    var type(x) w;\n"
      "    var type(P) u;\n"
      "  endclass\n"
      "  int rw, ru;\n"
      "  C c;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    c.w = -5;\n"
      "    c.u = 5'h1F;\n"
      "    rw = c.w;\n"
      "    ru = c.u;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"rw", 0xFFFFFFFBu}, {"ru", 0xFu}});
}

// §6.23 with A.2.7, A.2.8 and A.6.8: a class method's formal, a variable its
// body declares and a for loop's variable may each take their type by a type
// reference, which finds the class's property x before anything around the
// class. y, v and i are each an int, so f(-5) adds -2 and -1 to -5 and returns
// -8, where one-bit ones returned 1. A class nested in C reaches C's
// properties the same way, so the inner object's z holds -5 for g to return.
// `type(this)` names no property and nothing of the unit, and stands as
// written for the method's evaluation (§8.11).
TEST(TypeReferenceScopeSim, ClassMethodsAndNestedClassesOfTheClassesNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  class I;\n"
      "    var type(x) z;\n"
      "  endclass\n"
      "  function int f(input var type(x) y);\n"
      "    var type(x) v = y;\n"
      "    for (var type(x) i = -2; i < 0; i++) v += i;\n"
      "    return v;\n"
      "  endfunction\n"
      "  function int g();\n"
      "    I inner = new;\n"
      "    inner.z = -5;\n"
      "    return inner.z;\n"
      "  endfunction\n"
      "  function C me();\n"
      "    var type(this) h = this;\n"
      "    return h;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  C c;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    r1 = c.f(-5);\n"
      "    r2 = c.g();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 0xFFFFFFF8u}, {"r2", 0xFFFFFFFBu}});
}

// §6.23 with §26.2 and §3.12.1: a subroutine of a package or of the
// compilation unit may type a formal, or a variable its body declares, by a
// type reference to a value its scope declares, and a class of a package may
// type a property so. y, v and w are the package's int and z and q the
// unit's, so -5 stands whole in each, where a one-bit one held 1.
TEST(TypeReferenceScopeSim, PackageAndUnitSubroutinesOfTheirScopesNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  int x;\n"
      "  function automatic int f(input var type(x) y);\n"
      "    var type(x) v = y;\n"
      "    return v;\n"
      "  endfunction\n"
      "  class K;\n"
      "    var type(x) w;\n"
      "  endclass\n"
      "endpackage\n"
      "int ux;\n"
      "function automatic int h(input var type(ux) z);\n"
      "  return z;\n"
      "endfunction\n"
      "task automatic tk(input var type(ux) q, output int o);\n"
      "  o = q;\n"
      "endtask\n"
      "module t;\n"
      "  int r1, r2, r3, r4;\n"
      "  p::K k;\n"
      "  initial begin\n"
      "    r1 = p::f(-5);\n"
      "    r2 = h(-5);\n"
      "    k = new;\n"
      "    k.w = -5;\n"
      "    r3 = k.w;\n"
      "    tk(-5, r4);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 0xFFFFFFFBu},
                    {"r2", 0xFFFFFFFBu},
                    {"r3", 0xFFFFFFFBu},
                    {"r4", 0xFFFFFFFBu}});
}

}  // namespace
