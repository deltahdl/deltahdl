#include <gtest/gtest.h>

#include <format>
#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

constexpr std::initializer_list<std::string_view> kEveryPlace = {
    "module",         "interface", "program",
    "checker",        "package",   "compilation unit",
    "generate block", "class",     "function",
    "task",           "block"};

std::string OkIn(std::string_view place, std::string_view decls,
                 std::string_view check) {
  if (place == "module") {
    return std::format(
        "module m;\n{}  bit ok;\n  initial ok = {};\nendmodule\n", decls,
        check);
  }
  if (place == "interface" || place == "program") {
    const std::string_view kWord = place;
    return std::format(
        "{0} x;\n{1}  bit ok;\n  initial ok = {2};\nend{0}\n"
        "module m;\n  x u();\nendmodule\n",
        kWord, decls, check);
  }
  if (place == "checker") {
    return std::format(
        "checker x;\n{}  bit ok;\n  always_comb ok = {};\nendchecker\n"
        "module m;\n  x u();\nendmodule\n",
        decls, check);
  }
  if (place == "package") {
    return std::format(
        "package q;\n{}endpackage\nmodule m;\n  import q::*;\n  bit ok;\n"
        "  initial ok = {};\nendmodule\n",
        decls, check);
  }
  if (place == "compilation unit") {
    return std::format(
        "{}module m;\n  bit ok;\n  initial ok = {};\nendmodule\n", decls,
        check);
  }
  if (place == "generate block") {
    return std::format(
        "module m;\n  bit ok;\n  if (1) begin : g\n{}    initial ok = {};\n"
        "  end\nendmodule\n",
        decls, check);
  }
  if (place == "class") {
    return std::format(
        "class K;\n{}  function bit f();\n    return {};\n  endfunction\n"
        "endclass\nmodule m;\n  bit ok;\n  K k;\n"
        "  initial begin\n    k = new;\n    ok = k.f();\n  end\nendmodule\n",
        decls, check);
  }
  if (place == "function") {
    return std::format(
        "module m;\n  bit ok;\n  function automatic bit f();\n{}"
        "    return {};\n  endfunction\n  initial ok = f();\nendmodule\n",
        decls, check);
  }
  if (place == "task") {
    return std::format(
        "module m;\n  bit ok;\n  task automatic t(output bit o);\n{}"
        "    o = {};\n  endtask\n  initial t(ok);\nendmodule\n",
        decls, check);
  }
  return std::format(
      "module m;\n  bit ok;\n  initial begin\n{}    ok = {};\n  end\n"
      "endmodule\n",
      decls, check);
}

std::string_view OkNameIn(std::string_view place) {
  if (place == "interface" || place == "program" || place == "checker") {
    return "u.ok";
  }
  return "ok";
}

void ExpectOkIn(std::initializer_list<std::string_view> places,
                std::string_view decls, std::string_view check) {
  for (std::string_view place : places) {
    SCOPED_TRACE(place);
    const std::string kSrc = OkIn(place, decls, check);
    SCOPED_TRACE(kSrc);
    EXPECT_EQ(RunAndGet(kSrc, std::string(OkNameIn(place)).c_str()), 1u);
  }
}

constexpr std::string_view kTypedefBaseDecls =
    "  typedef bit [5:0] t;\n"
    "  typedef enum t {A, B} e_t;\n"
    "  e_t v;\n"
    "  typedef enum t [1:0] {F, G} f_t;\n"
    "  f_t fv;\n"
    "  typedef enum t {H, I} [2:0] g_t;\n"
    "  g_t gv;\n";

constexpr std::string_view kTypedefBaseStruct =
    "  typedef struct packed { e_t a; bit b; } s_t;\n"
    "  s_t sv;\n";

constexpr std::string_view kTypedefBaseVariablesCheck =
    "$bits(v) == 6 && $bits(A) == 6 && $bits(fv) == 12 && $bits(gv) == 18";

constexpr std::string_view kTypedefBaseTypeNamesCheck =
    "$bits(e_t) == 6 && $bits(f_t) == 12 && $bits(g_t) == 18";

constexpr std::initializer_list<std::string_view>
    kOutsideAClassSubroutineOrBlock = {
        "module",  "interface",        "program",       "checker",
        "package", "compilation unit", "generate block"};

TEST(EnumerationTypedefBaseSimulation, TypedefBaseGivesItsWidthInEveryPlace) {
  ExpectOkIn(kEveryPlace, kTypedefBaseDecls, kTypedefBaseVariablesCheck);
}

TEST(EnumerationTypedefBaseSimulation,
     DISABLED_TypeNamesOfATypedefBaseEnumerationGiveItsWidthInAClass) {
  ExpectOkIn({"class"}, kTypedefBaseDecls, kTypedefBaseTypeNamesCheck);
}

TEST(EnumerationTypedefBaseSimulation,
     DISABLED_StructOfATypedefBaseEnumerationIsAsWideAsItsMembersInAClass) {
  ExpectOkIn({"class"},
             std::string(kTypedefBaseDecls) + std::string(kTypedefBaseStruct),
             "$bits(sv) == 7 && $bits(s_t) == 7");
}

TEST(EnumerationTypedefBaseSimulation,
     TypeNamesOfATypedefBaseEnumerationGiveItsWidth) {
  ExpectOkIn(kOutsideAClassSubroutineOrBlock, kTypedefBaseDecls,
             kTypedefBaseTypeNamesCheck);
}

TEST(EnumerationTypedefBaseSimulation,
     DISABLED_LocalTypeNamesOfATypedefBaseEnumerationGiveItsWidth) {
  ExpectOkIn({"function", "task", "block"}, kTypedefBaseDecls,
             kTypedefBaseTypeNamesCheck);
}

TEST(EnumerationTypedefBaseSimulation,
     StructOfATypedefBaseEnumerationIsAsWideAsItsMembers) {
  ExpectOkIn(kOutsideAClassSubroutineOrBlock,
             std::string(kTypedefBaseDecls) + std::string(kTypedefBaseStruct),
             "$bits(sv) == 7 && $bits(s_t) == 7");
}

TEST(EnumerationTypedefBaseSimulation,
     DISABLED_LocalStructOfATypedefBaseEnumerationIsAsWideAsItsMembers) {
  ExpectOkIn({"function", "task", "block"},
             std::string(kTypedefBaseDecls) + std::string(kTypedefBaseStruct),
             "$bits(sv) == 7");
}

TEST(EnumerationTypedefBaseSimulation,
     TypedefOfATypedefGivesItsWidthInEveryPlace) {
  ExpectOkIn(kEveryPlace,
             "  typedef logic [5:0] t;\n"
             "  typedef t u;\n"
             "  typedef t [1:0] w;\n"
             "  typedef shortint s;\n"
             "  typedef s z;\n"
             "  enum u {UA, UB} uv;\n"
             "  enum w {WA, WB} wv;\n"
             "  enum u [2:0] {XA, XB} xv;\n"
             "  enum z {ZA = -3, ZB} zv;\n",
             "$bits(uv) == 6 && $bits(wv) == 12 && $bits(xv) == 18 && "
             "$bits(zv) == 16 && $isunknown(uv) && int'(ZA) == -3");
}

TEST(EnumerationTypedefBaseSimulation,
     WildcardImportedTypedefBaseGivesItsWidth) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef bit [5:0] t;\n"
                      "endpackage\n"
                      "module m;\n"
                      "  import p::*;\n"
                      "  enum t {A, B} v;\n"
                      "  bit ok;\n"
                      "  initial ok = $bits(v) == 6;\n"
                      "endmodule\n",
                      "ok"),
            1u);
}

TEST(EnumerationTypedefBaseSimulation,
     ShortintTypedefBaseIsSixteenBitsAndSignedInEveryPlace) {
  ExpectOkIn(kEveryPlace,
             "  typedef shortint s;\n"
             "  enum s {N = -5, O} v;\n",
             "$bits(v) == 16 && $bits(N) == 16 && int'(N) == -5 && "
             "int'(O) == -4");
}

TEST(EnumerationTypedefBaseSimulation,
     FourStateTypedefBaseStartsAtXAndTwoStateAtZeroInADesignElement) {
  ExpectOkIn({"module", "interface", "program", "checker", "generate block"},
             "  typedef logic [5:0] l;\n"
             "  typedef bit [5:0] t;\n"
             "  enum l {P, Q} lv;\n"
             "  enum t {R, S} tv;\n",
             "$isunknown(lv) && !$isunknown(tv) && tv == R");
}

TEST(EnumerationTypedefBaseSimulation,
     FourStateTypedefBaseStartsAtXAndTwoStateAtZeroElsewhere) {
  ExpectOkIn(
      {"package", "compilation unit", "class", "function", "task", "block"},
      "  typedef logic [5:0] l;\n"
      "  typedef bit [5:0] t;\n"
      "  enum l {P, Q} lv;\n"
      "  enum t {R, S} tv;\n",
      "$isunknown(lv) && !$isunknown(tv) && tv == R");
}

TEST(EnumerationTypedefBaseSimulation,
     FourStateKeywordBaseStartsAtXAndTwoStateAtZeroInEveryPlace) {
  ExpectOkIn(kEveryPlace,
             "  enum logic [5:0] {P, Q} lv;\n"
             "  enum bit [5:0] {R, S} tv;\n",
             "$isunknown(lv) && !$isunknown(tv) && tv == R");
}

TEST(EnumerationTypedefBaseSimulation,
     LocalFourStateEnumerationTypedefStartsAtXAndTwoStateAtZero) {
  ExpectOkIn({"function", "task", "block"},
             "  typedef enum logic [5:0] {P, Q} l_t;\n"
             "  typedef enum bit [5:0] {R, S} t_t;\n"
             "  l_t lv;\n"
             "  t_t tv;\n",
             "$isunknown(lv) && !$isunknown(tv) && tv == R");
}

TEST(EnumerationTypedefBaseSimulation,
     FourStateTypedefBaseIsAsWideAsItsTypedefInEveryPlace) {
  ExpectOkIn(kEveryPlace,
             "  typedef logic [5:0] l;\n"
             "  enum l {P, Q} lv;\n",
             "$bits(lv) == 6 && $bits(P) == 6");
}

TEST(EnumerationTypedefBaseSimulation, ImportedTypedefBaseGivesItsWidth) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef bit [5:0] t;\n"
                      "endpackage\n"
                      "module m;\n"
                      "  import p::t;\n"
                      "  typedef enum t {A, B} e_t;\n"
                      "  e_t v;\n"
                      "  bit ok;\n"
                      "  initial ok = $bits(e_t) == 6 && $bits(v) == 6;\n"
                      "endmodule\n",
                      "ok"),
            1u);
}

TEST(EnumerationTypedefBaseSimulation,
     LocalTypedefBaseHidesTheImportedOneOfItsName) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef bit [5:0] t;\n"
                      "endpackage\n"
                      "module m;\n"
                      "  import p::*;\n"
                      "  typedef bit [2:0] t;\n"
                      "  enum t {A, B} v;\n"
                      "  bit ok;\n"
                      "  initial ok = $bits(v) == 3;\n"
                      "endmodule\n",
                      "ok"),
            1u);
}

TEST(EnumerationTypedefBaseSimulation,
     StructMembersOfATypedefBaseEnumerationTakeTheirOffsets) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  typedef bit [5:0] t;\n"
                      "  typedef enum t {A, B} e_t;\n"
                      "  typedef struct packed { e_t a; e_t b; } s_t;\n"
                      "  s_t s;\n"
                      "  bit ok;\n"
                      "  initial begin\n"
                      "    s.a = B;\n"
                      "    s.b = A;\n"
                      "    ok = s === 12'b000001_000000 && s.a == B && "
                      "s.b == A;\n"
                      "  end\n"
                      "endmodule\n",
                      "ok"),
            1u);
}

TEST(EnumerationTypedefBaseSimulation,
     MethodsOfATypedefBaseEnumerationAreAsWideAsItsBase) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  typedef bit [5:0] t;\n"
                      "  typedef enum t {A, B} e_t;\n"
                      "  e_t v;\n"
                      "  bit ok;\n"
                      "  initial ok = $bits(v.first()) == 6 && "
                      "$bits(v.last()) == 6 && $bits(v.next()) == 6 && "
                      "$bits(v.prev()) == 6;\n"
                      "endmodule\n",
                      "ok"),
            1u);
}

std::string ClassEnumerationDesign(std::string_view reads) {
  return std::format(
      "package p;\n"
      "  localparam int PK = 20;\n"
      "endpackage\n"
      "parameter int UK = 30;\n"
      "import p::*;\n"
      "class c #(int P = 4);\n"
      "  localparam int K = 5;\n"
      "  typedef enum {{A = K, B = P, C = p::PK, D = PK + 1, E = UK, "
      "F = $unit::UK + 1, G = A + K + 100}} e_t;\n"
      "  enum {{H = K, I = P}} pv;\n"
      "  e_t ev;\n"
      "endclass\n"
      "module m;\n"
      "  c h;\n"
      "  c #(9) h9;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h9 = new;\n"
      "    h.ev = c#()::A;\n"
      "    h.pv = h.I;\n"
      "    $display({});\n"
      "  end\n"
      "endmodule\n",
      reads);
}

TEST(EnumerationClassSimulation,
     DISABLED_ClassEnumerationTakesTheClassLocalparamAndParameter) {
  SimFixture f;
  EXPECT_EQ(RunCapture(ClassEnumerationDesign(
                           "\"%0d %0d %0d %0d %s %s\", c#()::A, c#()::B, h.H, "
                           "h.I, h.ev.name(), h.pv.name()"),
                       f),
            "5 4 5 4 A I\n");
}

TEST(EnumerationClassSimulation,
     DISABLED_ClassEnumerationTakesEachSpecializationsOwnParameter) {
  SimFixture f;
  EXPECT_EQ(RunCapture(ClassEnumerationDesign(
                           "\"%0d %0d %0d %0d\", c#()::B, c#(9)::B, h.I, h9.I"),
                       f),
            "4 9 4 9\n");
}

TEST(EnumerationClassSimulation,
     DISABLED_ClassEnumerationTakesPackageAndUnitConstants) {
  SimFixture f;
  EXPECT_EQ(RunCapture(ClassEnumerationDesign(
                           "\"%0d %0d %0d %0d\", c#()::C, c#()::D, c#()::E, "
                           "c#()::F"),
                       f),
            "20 21 30 31\n");
}

TEST(EnumerationClassSimulation,
     DISABLED_ClassEnumerationValueOverEarlierMembersAndConstants) {
  SimFixture f;
  EXPECT_EQ(RunCapture(ClassEnumerationDesign("\"%0d\", c#()::G"), f), "110\n");
}

TEST(EnumerationClassSimulation,
     DISABLED_ClassEnumerationBaseSizedByAClassParameterTakesItsWidth) {
  EXPECT_EQ(RunAndGet("class c #(int W = 3);\n"
                      "  localparam int L = 5;\n"
                      "  typedef enum logic [W-1:0] {A, B} e_t;\n"
                      "  typedef enum bit [L-1:0] {X, Y} f_t;\n"
                      "  e_t v;\n"
                      "endclass\n"
                      "module m;\n"
                      "  c #(7) h;\n"
                      "  bit ok;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    ok = $bits(c#()::e_t) == 3 && $bits(c#()::f_t) == 5 "
                      "&& $bits(h.v) == 7;\n"
                      "  end\n"
                      "endmodule\n",
                      "ok"),
            1u);
}

TEST(EnumerationClassSimulation, ClassEnumerationWithLiteralValuesReadsThem) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class c;\n"
                 "  typedef enum logic [3:0] {A = 3, B} e_t;\n"
                 "  enum {C = 7, D} pv;\n"
                 "  e_t ev;\n"
                 "endclass\n"
                 "module m;\n"
                 "  c h;\n"
                 "  initial begin\n"
                 "    h = new;\n"
                 "    h.ev = c::B;\n"
                 "    h.pv = h.D;\n"
                 "    $display(\"%0d %0d %0d %0d %s %s %0d\", c::A, c::B, "
                 "h.C, h.D, h.ev.name(), h.pv.name(), $bits(c::e_t));\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "3 4 7 8 B D 4\n");
}

TEST(EnumerationClassSimulation,
     PropertyOfAClassEnumerationTypedefTakesItsBaseWidthAndStates) {
  ExpectOkIn({"class"},
             "  typedef enum bit [5:0] {A, B} b_t;\n"
             "  typedef enum logic [2:0] {P, Q} l_t;\n"
             "  typedef b_t c_t;\n"
             "  b_t bv;\n"
             "  l_t lv;\n"
             "  c_t cv;\n",
             "$bits(bv) == 6 && $bits(lv) == 3 && $bits(cv) == 6 && "
             "!$isunknown(bv) && $isunknown(lv)");
}

constexpr std::string_view kFourStateConstantParameters =
    "package pk;\n"
    "  typedef enum logic [1:0] {PA = 0, PX = 2'bx1} e_t;\n"
    "endpackage\n"
    "typedef enum logic [1:0] {UA = 0, UZ = 'z} u_t;\n"
    "class K;\n"
    "  typedef enum logic [1:0] {KA = 0, KX = 'x} k_t;\n"
    "endclass\n"
    "module s #(parameter logic [1:0] Q = 0);\n"
    "  typedef enum logic [1:0] {SA = 0, SX = 2'b1x} s_t;\n"
    "  localparam logic [1:0] SP = SX;\n"
    "  logic [1:0] sw = SP;\n"
    "  bit ok;\n"
    "  bit own_ok;\n"
    "  initial begin\n"
    "    ok = Q === 2'bxx;\n"
    "    own_ok = SP === 2'b1x && sw === 2'b1x;\n"
    "  end\n"
    "endmodule\n"
    "module m;\n"
    "  typedef enum logic [1:0] {A = 0, XX = 'x, ZZ = 'z} m_t;\n"
    "  enum logic [1:0] {IA = 0, IX = 2'bx0} iv;\n"
    "  parameter logic [1:0] P1 = XX;\n"
    "  localparam m_t P2 = ZZ;\n"
    "  localparam P3 = XX | 2'b00;\n"
    "  localparam P4 = IX;\n"
    "  localparam logic [1:0] P5 = pk::PX;\n"
    "  localparam P6 = UZ;\n"
    "  localparam P7 = K::KX;\n"
    "  localparam bit [1:0] P8 = XX;\n"
    "  logic [1:0] w1 = P1;\n"
    "  s #(.Q(XX)) u();\n"
    "  bit ok;\n"
    "  bit class_ok;\n"
    "  bit two_state_ok;\n"
    "  initial begin\n"
    "    ok = P1 === 2'bxx && P2 === 2'bzz && P3 === 2'bxx && P4 === 2'bx0 &&\n"
    "         P5 === 2'bx1 && P6 === 2'bzz && w1 === 2'bxx;\n"
    "    class_ok = P7 === 2'bxx;\n"
    "    two_state_ok = P8 === 2'b00;\n"
    "  end\n"
    "endmodule\n";

TEST(EnumerationParameterSimulation,
     ParameterGivenAnXOrZEnumerationConstantKeepsItsBits) {
  EXPECT_EQ(RunAndGet(std::string(kFourStateConstantParameters), "ok"), 1u);
}

TEST(EnumerationParameterSimulation,
     ChildParameterGivenItsOwnXEnumerationConstantKeepsItsBits) {
  EXPECT_EQ(RunAndGet(std::string(kFourStateConstantParameters), "u.own_ok"),
            1u);
}

TEST(EnumerationParameterSimulation,
     DISABLED_ParameterGivenAClassXEnumerationConstantKeepsItsBits) {
  EXPECT_EQ(RunAndGet(std::string(kFourStateConstantParameters), "class_ok"),
            1u);
}

TEST(EnumerationParameterSimulation,
     ParameterPortOverrideGivenAnXEnumerationConstantKeepsItsBits) {
  EXPECT_EQ(RunAndGet(std::string(kFourStateConstantParameters), "u.ok"), 1u);
}

TEST(EnumerationParameterSimulation,
     TwoStateParameterGivenAnXEnumerationConstantHoldsZero) {
  EXPECT_EQ(
      RunAndGet(std::string(kFourStateConstantParameters), "two_state_ok"), 1u);
}

TEST(EnumerationEarlierConstantSimulation,
     EarlierConstantsGiveTheirValuesInEveryPlace) {
  ExpectOkIn(kEveryPlace,
             "  enum {A = 2, B = A * 3, C, D = C - B} e;\n"
             "  typedef enum {R[2] = 5, S = R1 * 2, T = S + R0} r_t;\n",
             "A == 2 && B == 6 && C == 7 && D == 1 && R0 == 5 && R1 == 6 && "
             "S == 12 && T == 17");
}

}  // namespace
