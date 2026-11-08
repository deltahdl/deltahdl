#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

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

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsABlockVariablesMember) {
  const std::string kSrc =
      "module t;\n"
      "  typedef struct packed { bit [7:0] f; bit g; } st;\n"
      "  bit [3:0] n;\n"
      "  int d;\n"
      "  initial begin\n"
      "    st q;\n"
      "    d = type(n + q.f)'(16'hABCF);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xCFu);
}

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

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsClog2AsAnInteger) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  logic [7:0] m;\n"
      "  int d;\n"
      "  initial d = type(n + $clog2(m))'(16'hABCF);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xABCFu);
}

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsAnArrayQueryAsAnInteger) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  logic [7:0] m;\n"
      "  int d;\n"
      "  initial d = type(n + $size(m))'(16'hABCF);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xABCFu);
}

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsBitVectorFunctionsTypes) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  logic [7:0] m;\n"
      "  byte s;\n"
      "  logic [15:0] v = 16'hABCx;\n"
      "  int d, e;\n"
      "  bit u;\n"
      "  initial begin\n"
      "    d = type(n + $countones(m))'(16'hABCF);\n"
      "    e = type(s + $onehot(m))'(16'h00F0);\n"
      "    u = $isunknown(type(n + $isunknown(m))'(v));\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xABCFu);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0xF0u);
  EXPECT_EQ(RunAndGet(kSrc, "u"), 0u);
}

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsTimeFunctionsTypes) {
  const std::string kSrc =
      "module t;\n"
      "  bit [3:0] n;\n"
      "  byte s;\n"
      "  int d, e;\n"
      "  initial begin\n"
      "    d = type(n + $time)'(16'hABCF);\n"
      "    e = type(s + $stime)'(16'h00F0);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xABCFu);
  EXPECT_EQ(RunAndGet(kSrc, "e"), 0xF0u);
}

TEST(TypeOfExprCastSim, CastToATypeReferenceReadsAPackageVariablesMember) {
  const std::string kSrc =
      "package pkg;\n"
      "  typedef struct packed { bit [7:0] f; bit g; } st;\n"
      "  st v;\n"
      "endpackage\n"
      "module t;\n"
      "  bit [3:0] n;\n"
      "  int d;\n"
      "  initial d = type(n + pkg::v.f)'(16'hABCF);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "d"), 0xCFu);
}

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
