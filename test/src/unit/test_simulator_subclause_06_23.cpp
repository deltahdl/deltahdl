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

// §6.23 with §11.6.1 and §11.8.1: a type reference to an operation is the
// operation's self-determined type, which the expression's form gives without
// evaluating it, so with `bit [3:0] n` the cast to `type(n + n)` keeps the low
// four bits of 16'hABCF, 15, and with `byte s` the cast to `type(s + s)` makes
// 16'h00F0 the signed -16.
TEST(TypeOfExprCastSim, CastToATypeReferenceOfAnOperationTakesItsSizeAndSign) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  byte s;\n"
      "  int d, e;\n"
      "  initial begin\n"
      "    d = type(n + n)'(16'hABCF);\n"
      "    e = type(s + s)'(16'h00F0);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 15u);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0xFFFFFFF0u);
}

// §6.23 with §11.3.4: an operation on 2-state operands only is 2-state, so a
// cast to its type reads an x of the value as 0, while one 4-state operand, the
// condition of a conditional among them, or a literal makes it 4-state and the
// x stays. Each bit of r says whether the cast's result holds an unknown.
TEST(TypeOfExprCastSim,
     CastToATypeReferenceOfAnOperationIs2StateOnlyFrom2State) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  bit c;\n"
      "  logic l;\n"
      "  logic [3:0] m;\n"
      "  logic [15:0] v = 16'hABCx;\n"
      "  bit [8:0] r;\n"
      "  initial r = {$isunknown(type(n + n)'(v)), $isunknown(type(-n)'(v)),\n"
      "               $isunknown(type(c ? n : n)'(v)),\n"
      "               $isunknown(type(n + m)'(v)),\n"
      "               $isunknown(type(m + n)'(v)),\n"
      "               $isunknown(type(l ? n : n)'(v)),\n"
      "               $isunknown(type(c ? m : n)'(v)),\n"
      "               $isunknown(type(c ? n : m)'(v)),\n"
      "               $isunknown(type(n + 1)'(v))};\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0x3Fu);
}

// §6.23 with §11.5.1 and §11.8.1: a select in the expression a type reference
// names is as wide as the bits or elements it selects -- eight for `a[7:0]`
// and for an element `p[1]` of a packed array of bytes, six for `a[i +: 6]`
// and `a[9 -: 6]` -- unsigned, and 2-state where the selected variable is; an
// element of an unpacked array of bytes is a byte.
TEST(TypeOfExprCastSim, CastToATypeReferenceReadsASelectsType) {
  const std::string kSrc =
      "module t;\n"
      "  logic [15:0] a;\n"
      "  logic [3:0][7:0] p;\n"
      "  bit [7:0] b;\n"
      "  bit [3:0] n;\n"
      "  byte s;\n"
      "  byte mem [4];\n"
      "  int i = 2;\n"
      "  logic [15:0] v = 16'hABCx;\n"
      "  int d, e, f, g, h, j, k;\n"
      "  bit u;\n"
      "  initial begin\n"
      "    d = type(a[7:0] + n)'(16'hABCF);\n"
      "    e = type(a[11:4])'(16'h1234);\n"
      "    f = type(a[i +: 6])'(16'h00FF);\n"
      "    j = type(a[9 -: 6])'(16'h00FF);\n"
      "    g = type(p[1] + n)'(16'hABCF);\n"
      "    h = type(a[7:0] + s)'(16'h00F0);\n"
      "    k = type(mem[0] + n)'(16'h00F0);\n"
      "    u = $isunknown(type(b[3:0] + n)'(v));\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xCFu);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0x34u);
  EXPECT_EQ(RunAndGet(kSrc, "f"), 0x3Fu);
  EXPECT_EQ(RunAndGet(kSrc, "j"), 0x3Fu);
  EXPECT_EQ(RunAndGet(kSrc, "g"), 0xCFu);
  EXPECT_EQ(RunAndGet(kSrc, "h"), 0xF0u);
  EXPECT_EQ(RunAndGet(kSrc, "k"), 0xF0u);
  EXPECT_EQ(RunAndGet(kSrc, "u"), 0u);
}

// §6.23 with §7.2: a member of a structure in the expression a type reference
// names has its member's type, here eight unsigned 2-state bits.
TEST(TypeOfExprCastSim, CastToATypeReferenceReadsAMembersType) {
  const std::string kSrc =
      "module t;\n"
      "  typedef struct packed { bit [7:0] f; bit g; } st;\n"
      "  st p;\n"
      "  bit [3:0] n;\n"
      "  byte s;\n"
      "  logic [15:0] v = 16'hABCx;\n"
      "  int d, e;\n"
      "  bit u;\n"
      "  initial begin\n"
      "    d = type(n + p.f)'(16'hABCF);\n"
      "    e = type(s + p.f)'(16'h00F0);\n"
      "    u = $isunknown(type(n + p.f)'(v));\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xCFu);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0xF0u);
  EXPECT_EQ(RunAndGet(kSrc, "u"), 0u);
}

// §6.23 with §11.4.12: a concatenation in the expression a type reference
// names is as wide as its operands together, and 2-state where they all are.
TEST(TypeOfExprCastSim, CastToATypeReferenceReadsAConcatenationsType) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  bit c;\n"
      "  logic [15:0] v = 16'hABCx;\n"
      "  int d;\n"
      "  bit u;\n"
      "  initial begin\n"
      "    d = type(n + {n, n})'(16'hABCF);\n"
      "    u = $isunknown(type(c + {c, c})'(v));\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xCFu);
  EXPECT_EQ(RunAndGet(kSrc, "u"), 0u);
}

// §6.23 with §11.4.12.1: a replication in the expression a type reference
// names is its count times as wide as its operands, and unsigned.
TEST(TypeOfExprCastSim, CastToATypeReferenceReadsAReplicationsType) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  byte s;\n"
      "  int d, e;\n"
      "  initial begin\n"
      "    d = type(n + {2{n}})'(16'hABCF);\n"
      "    e = type(s + {2{n}})'(16'h00F0);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xCFu);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0xF0u);
}

// §6.23 with §13.4: a function call in the expression a type reference names
// has the function's return type, here a 2-state byte, and the function is
// not called, so `calls` stays 0.
TEST(TypeOfExprCastSim, CastToATypeReferenceReadsACallsReturnType) {
  const std::string kSrc =
      "module t;\n"
      "  int calls;\n"
      "  bit [3:0] n;\n"
      "  logic [15:0] v = 16'hABCx;\n"
      "  int d;\n"
      "  bit u;\n"
      "  function byte f(int x);\n"
      "    calls++;\n"
      "    return x;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    d = type(n + f(0))'(16'hABCF);\n"
      "    u = $isunknown(type(n + f(0))'(v));\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xCFu);
  EXPECT_EQ(RunAndGet(kSrc, "u"), 0u);
  EXPECT_EQ(RunAndGet(kSrc, "calls"), 0u);
}

// §6.23 with §6.24.1: a cast in the expression a type reference names has its
// casting type -- a byte, eight bits for a size cast, a typedef's type, the
// type a type reference names -- and a signing cast makes its operand's type
// signed or unsigned.
TEST(TypeOfExprCastSim, CastToATypeReferenceReadsAnInnerCastsType) {
  const std::string kSrc =
      "module t;\n"
      "  typedef logic [7:0] w_t;\n"
      "  bit [3:0] n;\n"
      "  bit [7:0] b;\n"
      "  byte s;\n"
      "  logic [15:0] v = 16'hABCx;\n"
      "  int d, e, f, g, h, k;\n"
      "  bit u;\n"
      "  initial begin\n"
      "    d = type(n + byte'(s))'(16'hABCF);\n"
      "    e = type(n + 8'(n))'(16'hABCF);\n"
      "    f = type(s + unsigned'(s))'(16'h00F0);\n"
      "    g = type(n + w_t'(n))'(16'hABCF);\n"
      "    h = type(n + signed'(b))'(16'hABCF);\n"
      "    k = type(n + type(b)'(n))'(16'hABCF);\n"
      "    u = $isunknown(type(n + byte'(s))'(v));\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xCFu);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0xCFu);
  EXPECT_EQ(RunAndGet(kSrc, "f"), 0xF0u);
  EXPECT_EQ(RunAndGet(kSrc, "g"), 0xCFu);
  EXPECT_EQ(RunAndGet(kSrc, "h"), 0xCFu);
  EXPECT_EQ(RunAndGet(kSrc, "k"), 0xCFu);
  EXPECT_EQ(RunAndGet(kSrc, "u"), 0u);
}

// §6.23 with §11.7 and §20.6.2: `$signed` and `$unsigned` in the expression a
// type reference names are as wide and as 2- or 4-state as their argument,
// signed or unsigned as each names, and `$bits` is a 32-bit integer.
TEST(TypeOfExprCastSim, CastToATypeReferenceReadsASystemFunctionsType) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  bit [7:0] b;\n"
      "  logic [7:0] m;\n"
      "  byte s;\n"
      "  logic [15:0] v = 16'hABCx;\n"
      "  int d, e, f;\n"
      "  bit u;\n"
      "  initial begin\n"
      "    d = type(n + $unsigned(m))'(16'hABCF);\n"
      "    e = type(s + $unsigned(s))'(16'h00F0);\n"
      "    f = type(n + $bits(m))'(16'hABCF);\n"
      "    u = $isunknown(type(n + $signed(b))'(v));\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xCFu);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0xF0u);
  EXPECT_EQ(RunAndGet(kSrc, "f"), 0xABCFu);
  EXPECT_EQ(RunAndGet(kSrc, "u"), 0u);
}

// §6.23 with §6.24.1 and §6.11.3: a type reference to an integer atom type
// written unsigned casts to that unsigned type, so -1 cast to `int unsigned`
// compares above 0 and -1 cast to `byte unsigned` widens with zeros to 255,
// while `shortint` written alone keeps its signed default and 16'hFFFF cast
// to it compares below 0.
TEST(TypeOfExprCastSim, CastToATypeReferenceTakesTheWrittenSigning) {
  const std::string kSrc =
      "module t;\n"
      "  bit r, n;\n"
      "  int w;\n"
      "  initial begin\n"
      "    r = type(int unsigned)'(-1) > 0;\n"
      "    w = type(byte unsigned)'(-1);\n"
      "    n = type(shortint)'(16'hFFFF) < 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "w"), 255u);
  EXPECT_EQ(RunAndGet(kSrc, "n"), 1u);
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

// §6.23 with §6.20.2, §26.2 and §3.12.1: a parameter of a package or of the
// compilation unit declared with neither type nor range takes its value's
// type, whose names are the parameters its own scope declares ahead of it.
// P's Q is the package's 32-bit 3 and UP's UQ the unit's int, so each sum is
// 32 bits and every variable typed after P or UP holds -5 whole: through the
// package's typedef, the unit's typedef, an import, a `p::` prefix and a
// module's reference to the unit. Read among the module's names, where no Q or
// UQ is declared, each sum took the 4 bits of its literal and held 4'hB.
TEST(TypeReferenceScopeSim, UntypedParametersOfTheirScopesParameters) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter R = 1;\n"
      "  parameter Q = 3;\n"
      "  parameter P = Q + 4'd1;\n"
      "  typedef type(P) t;\n"
      "endpackage\n"
      "parameter int UQ = 3;\n"
      "parameter UP = UQ + 4'd1;\n"
      "typedef type(UP) ut;\n"
      "module t;\n"
      "  import p::*;\n"
      "  p::t a;\n"
      "  ut b;\n"
      "  var type(P) c;\n"
      "  var type(p::P) d;\n"
      "  var type(UP) e;\n"
      "  initial begin\n"
      "    a = -5;\n"
      "    b = -5;\n"
      "    c = -5;\n"
      "    d = -5;\n"
      "    e = -5;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"a", 0xFFFFFFFBu},
                    {"b", 0xFFFFFFFBu},
                    {"c", 0xFFFFFFFBu},
                    {"d", 0xFFFFFFFBu},
                    {"e", 0xFFFFFFFBu}});
}

// §6.23 with §6.20.2, §6.19 and §6.19.3: a parameter of a package or of the
// compilation unit declared with neither type nor range whose value is an
// enumeration constant takes the enumeration's type, an int by default. PE is
// E1's, PF the F1 that `F[2]` generates, and UPE the unit's U1, so each typed
// after them is 32 bits and holds -5 whole, through a typedef or a `p::`
// prefix. Looked up among parameters alone, each constant added no width,
// and each variable was one bit holding 1.
TEST(TypeReferenceScopeSim, UntypedParametersOfEnumerationConstants) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef enum {E0, E1} e_t;\n"
      "  typedef enum {F[2]} f_t;\n"
      "  parameter PE = E1;\n"
      "  parameter PF = F1;\n"
      "  typedef type(PE) et;\n"
      "  typedef type(PF) ft;\n"
      "endpackage\n"
      "typedef enum {U0, U1} u_t;\n"
      "parameter UPE = U1;\n"
      "typedef type(UPE) uet;\n"
      "module t;\n"
      "  p::et a;\n"
      "  p::ft b;\n"
      "  uet c;\n"
      "  var type(p::PE) d;\n"
      "  initial begin\n"
      "    a = -5;\n"
      "    b = -5;\n"
      "    c = -5;\n"
      "    d = -5;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"a", 0xFFFFFFFBu},
                    {"b", 0xFFFFFFFBu},
                    {"c", 0xFFFFFFFBu},
                    {"d", 0xFFFFFFFBu}});
}

// §6.23 with §5.7.1: a type reference to a simple decimal number stands for a
// signed type, and one to a based literal for a signed type only where its
// base carries s. So a, of type(3), compares below 0 after -5, and b, of
// type(4'sd1), widens its -1 to an int's -1, where c, of type(4'd1), widens
// it to 15. A package's parameter of no type valued 3 is signed the same way,
// and d, typed after it, compares below 0. Each literal was read unsigned,
// and a and d compared above 0 while b widened to 15.
TEST(TypeReferenceScopeSim, LiteralTypeReferencesTakeTheLiteralsSigning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter P = 3;\n"
      "  typedef type(P) t;\n"
      "endpackage\n"
      "module t;\n"
      "  var type(3) a;\n"
      "  var type(4'sd1) b;\n"
      "  var type(4'd1) c;\n"
      "  p::t d;\n"
      "  int ra, rb, rc, rd;\n"
      "  initial begin\n"
      "    a = -5;\n"
      "    b = -1;\n"
      "    c = -1;\n"
      "    d = -5;\n"
      "    ra = a < 0;\n"
      "    rb = b;\n"
      "    rc = c;\n"
      "    rd = d < 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"ra", 1u}, {"rb", 0xFFFFFFFFu}, {"rc", 0xFu}, {"rd", 1u}});
}

}  // namespace
