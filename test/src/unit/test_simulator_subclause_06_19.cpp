#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <format>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(EnumerationSimulation, DefaultIntBaseTypeWidthAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  enum {IDLE, BUSY, DONE} state;\n"
      "  int observed;\n"
      "  initial begin\n"
      "    state = BUSY;\n"
      "    observed = state;\n"
      "  end\n"
      "endmodule\n",
      f, "state");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
}

TEST(EnumerationSimulation, AutoIncrementedValuesPropagateAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  typedef enum {ZERO, ONE, TWO} count_t;\n"
      "  int observed;\n"
      "  initial begin\n"
      "    observed = TWO;\n"
      "  end\n"
      "endmodule\n",
      f, "observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §6.19: an enum named-constant value is an elaboration-time constant
// expression (§6.20). End-to-end: a value seeded from a real parameter feeds
// the auto-increment cursor and propagates at runtime (A=BASE=10, B=A+1=11).
TEST(EnumerationSimulation, ParameterSeededEnumValuePropagatesAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  parameter int BASE = 10;\n"
      "  enum integer {A = BASE, B} e;\n"
      "  int observed;\n"
      "  initial observed = B;\n"
      "endmodule\n",
      f, "observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

// §6.19: an enumerated type declares a set of named integral constants, and
// Syntax 6-5 places the enum form among the data_type productions, so the
// clause's own example -- `enum {red, yellow, green} light1, light2;` -- gives
// red, yellow and green values without any typedef. Read one back at runtime:
// green is the third member of a zero-based auto-increment, so it is 2.
TEST(EnumerationSimulation, BareEnumDeclarationNamesConstantsAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  enum {red, yellow, green} light1;\n"
      "  int observed;\n"
      "  initial observed = green;\n"
      "endmodule\n",
      f, "observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §6.19: the same enumeration may be shared by several declarators, as the
// clause's `light1, light2` example is. Its named constants are declared once
// for the enumeration, not once per variable, so the second declarator must
// neither redeclare them nor disturb the values the first gave them.
TEST(EnumerationSimulation, SharedEnumDeclaresItsConstantsOnce) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  enum {red, yellow, green} light1, light2;\n"
      "  int observed;\n"
      "  initial observed = yellow;\n"
      "endmodule\n",
      f, "observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §6.19 (printed page 119) has an enumerated type declare its literals as
// named constants of the scope holding the enum, §7.2's Syntax 7-1 (printed
// 146) gives a structure member any data_type, the enum form among them, and
// §23.9's list of scope-defining elements (printed 761) names no structure,
// so IDLE and BUSY are constants of p, read at run time through §26.3's
// package scope resolution operator and by their bare names through the
// wildcard import: 1 * 100 + 1 * 10 + 0 = 110. Before, the package's
// run-time "p.BUSY" constant and the import's backing variable were each
// created for an enumeration written at the top of a typedef alone, and
// `p::BUSY` read 0.
TEST(EnumerationSimulation, StructMemberEnumLiteralOfAPackageReadsAtRuntime) {
  EXPECT_EQ(
      RunAndGet("package p;\n"
                "  typedef struct { enum {IDLE, BUSY} st; int n; } s_t;\n"
                "endpackage\n"
                "module top;\n"
                "  import p::*;\n"
                "  int observed;\n"
                "  initial observed = p::BUSY * 100 + BUSY * 10 + p::IDLE;\n"
                "endmodule\n",
                "observed"),
      110u);
}

// The same for a module's own typedef: the member's enumeration declares A
// and B in the module, numbered from 0 (printed 120), so B * 10 + A is 10.
// Before, `B` was reported an unresolved identifier, the module declaring the
// constants of a typedef naming the enum form alone.
TEST(EnumerationSimulation, StructMemberEnumLiteralOfAModuleReadsAtRuntime) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { enum {A, B} e; int n; } t;\n"
                      "  int observed;\n"
                      "  initial observed = B * 10 + A;\n"
                      "endmodule\n",
                      "observed"),
            10u);
}

// §6.19 (printed page 119) has an enumerated type declare its literals as
// named constants of the scope holding it, and Syntax 6-5 makes the enum form
// a data_type, so p's `enum {X, Y} v;` declares X and Y in p with no typedef,
// and §26.3 (printed 810) makes each a candidate the wildcard import brings
// in: Y * 10 + X is 1 * 10 + 0 = 10. Before, the import's backing variables
// were emitted for a typedef's enumeration alone, so Y had no storage in the
// module and read nothing.
TEST(EnumerationSimulation, PackageBareEnumLiteralReadsThroughAWildcardImport) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  enum {X, Y} v;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int observed;\n"
                      "  initial observed = Y * 10 + X;\n"
                      "endmodule\n",
                      "observed"),
            10u);
}

// §3.12.1 (printed page 56) has the compilation-unit scope hold any item a
// package holds, a data declaration among them, visible to the modules of
// the unit written after it; §6.19 (printed 119) has an enumerated type
// declare its literals as constants of the scope holding it, Syntax 6-5
// making the enum form a data_type, so a unit-scope `enum {X, Y} v;`
// declares X and Y with no typedef, and the module reads Y * 10 + X as
// 1 * 10 + 0 = 10 at run time through the backing variables
// RegisterCuEnumLiterals gives it. Before, the parser admitted no enum head
// to a unit-scope data declaration (IsCuScopeDataTypeKeyword), reporting
// "expected top-level declaration", and RegisterCuEnumLiterals gave the
// module the backing variables of a typedef's enumeration alone.
TEST(EnumerationSimulation, UnitScopeBareEnumLiteralReadsAtRuntime) {
  EXPECT_EQ(RunAndGet("enum {X, Y} v;\n"
                      "module top;\n"
                      "  int observed;\n"
                      "  initial observed = Y * 10 + X;\n"
                      "endmodule\n",
                      "observed"),
            10u);
}

// The same clauses for a unit-scope typedef standing beside the bare
// declaration: the typedef's P and Q are declared as before, each enumeration
// numbering its literals from 0 on its own (printed 120), so Q * 10 + P is
// 1 * 10 + 0 = 10 with the bare declaration's X and Y in the same scope. The
// typedef path is the one RegisterCuEnumLiterals walked before f98562dad, and
// this pins it beside the data declaration the walk now reaches too.
TEST(EnumerationSimulation,
     UnitScopeTypedefEnumLiteralReadsBesideABareDeclaration) {
  EXPECT_EQ(RunAndGet("typedef enum {P, Q} t;\n"
                      "enum {X, Y} v;\n"
                      "module top;\n"
                      "  int observed;\n"
                      "  initial observed = Q * 10 + P;\n"
                      "endmodule\n",
                      "observed"),
            10u);
}

// §6.19 (printed page 119) has an enumeration's named constants be of its
// base type, so a member of `enum int` read in a display is a signed 32-bit
// value, and §5.7.1 (printed 79) has the sized signed literal `-8'sd6`
// sign-extended when it is widened: C is -6, which an unsigned reading of the
// same 32 bits prints as 4294967290. A and B alongside are the issue's other
// members, unchanged at 16 and 3.
TEST(EnumerationSimulation, NegativeMemberOfAnIntBaseEnumPrintsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef enum int {A = 'h10, B = 32'b1_1, C = -8'sd6} e_t;\n"
      "  initial $display(\"A=%0d B=%0d C=%0d\", A, B, C);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "A=16 B=3 C=-6\n");
}

// The same clause makes `int` the base type of an enumeration that names
// none, so a member of a bare `enum {...}` is signed too: -1 prints as -1
// rather than 4294967295.
TEST(EnumerationSimulation, NegativeMemberOfAnEnumWithNoBasePrintsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  enum {N = -1, P} e;\n"
      "  initial $display(\"N=%0d P=%0d\", N, P);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "N=-1 P=0\n");
}

// A variable of the enumerated type holds a value of the base type as well
// (§6.19.4), so the member read through the variable prints the same -6.
TEST(EnumerationSimulation, VariableOfAnIntBaseEnumPrintsItsMemberSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef enum int {A = 'h10, C = -8'sd6} e_t;\n"
      "  e_t v = C;\n"
      "  initial $display(\"v=%0d\", v);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "v=-6\n");
}

// A member of an enumeration over an unsigned base keeps the unsigned
// reading: `logic [3:0]` at 4'hF prints 15, not -1.
TEST(EnumerationSimulation, MemberOfALogicBaseEnumPrintsUnsigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef enum logic [3:0] {U = 4'hF} e_t;\n"
      "  initial $display(\"U=%0d\", U);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "U=15\n");
}

// §6.8 gives a variable declaration an initial value, and its data type may be
// written as an inline enumeration (A.2.2.1), `var enum bit { clear, error }
// status = error;` among §6.19's own examples. The declaration declares the
// members with the type, so the initializer reads them; each variable starts
// at its initializer, with or without `var`, as a variable of a typedef of the
// enumeration does.
TEST(EnumerationSimulation, InlineEnumVariableTakesItsInitializer) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  var enum bit { clear, error } s1 = error;\n"
      "  enum bit { c2, e2 } s2 = e2;\n"
      "  var enum { a3, b3, c3 } s3 = c3;\n"
      "  typedef enum bit {x4, y4} t4;\n"
      "  var t4 s4 = y4;\n"
      "  initial $display(\"%s %s %s %s %0d %0d\", s1.name(), s2.name(),\n"
      "                   s3.name(), s4.name(), s1, s3);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "error e2 c3 y4 1 2\n");
}

// The initializer of a later declarator of the list reads the members too, and
// one may name a member other than the first declarator's.
TEST(EnumerationSimulation, EachDeclaratorOfAnInlineEnumTakesItsInitializer) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  enum {a, b, c} u = c, w = b;\n"
      "  initial $display(\"%s %s %0d %0d\", u.name(), w.name(), u, w);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "c b 2 1\n");
}

// §6.19 lets a member of a 4-state enumeration be assigned x or z, its own
// example writing `XX='x` in an `integer` enumeration. The member constant
// holds that value, and so does a variable assigned it, while the members
// around it keep theirs; a z member of a `logic` enumeration holds z.
TEST(EnumerationSimulation, XOrZMemberOfA4StateEnumHoldsItsValue) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  enum integer {IDLE, XX='x, S1='b01, S2='b10} state;\n"
      "  enum logic [1:0] {A, Z='z, B=2} lz;\n"
      "  initial begin\n"
      "    state = XX; lz = Z;\n"
      "    $display(\"%0d %0d %0d %0d %0d %b %b\", $isunknown(XX), XX === 'x,\n"
      "             state === 'x, S1, S2, Z, lz);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 1 2 zz zz\n");
}

// A.2.8 admits a typedef among a block's items, in a begin-end block and in a
// task body, and §6.19 makes its enumeration's members named constants of
// the block, which the statements after it read; a variable declared with the
// typedef is of the enumeration, so §6.19.5's methods answer for it.
TEST(EnumerationSimulation, BlockTypedefEnumHasItsMembersAndVariables) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    typedef enum {p, q} e_t;\n"
      "    e_t z;\n"
      "    z = z.last();\n"
      "    $display(\"[%s] %0d %0d %0d\", z.name(), z, z.num(), q);\n"
      "  end\n"
      "  task automatic tk;\n"
      "    typedef enum {a1, b1} f_t;\n"
      "    int j;\n"
      "    j = b1;\n"
      "    $display(\"%0d\", j);\n"
      "  endtask\n"
      "  initial #1 tk();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[q] 1 2 1\n1\n");
}

// Each block's typedef is a type of that block alone (§23.9), so two blocks
// declaring `e_t` over different bases and members keep apart; a member value
// may name a parameter of the module; a function body's typedef is its own;
// and a `V[2]` member declares V0 and V1 (§6.19.2) in a fork's block.
TEST(EnumerationSimulation, BlockTypedefEnumsOfTheSameNameKeepApart) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  parameter int K = 5;\n"
      "  function automatic int fn();\n"
      "    typedef enum {m0 = K, m1} h_t;\n"
      "    h_t hv;\n"
      "    hv = m1;\n"
      "    return hv + hv.num();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    typedef enum bit [1:0] {p = 1, q = 3} e_t;\n"
      "    e_t z;\n"
      "    z = q;\n"
      "    $display(\"A %s %0d %0d %0d\", z.name(), z, $bits(z), z.num());\n"
      "  end\n"
      "  initial #1 begin\n"
      "    typedef enum {p, q, r} e_t;\n"
      "    e_t z;\n"
      "    z = r;\n"
      "    $display(\"B %s %0d %0d %0d\", z.name(), z, z.num(), fn());\n"
      "  end\n"
      "  initial #2 fork\n"
      "    begin\n"
      "      typedef enum {V[2], w} g_t;\n"
      "      g_t g;\n"
      "      g = V1;\n"
      "      $display(\"C %s %0d %0d\", g.name(), g, w);\n"
      "    end\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "A q 3 2 2\nB r 2 3 8\nC V1 1 2\n");
}

// A.2.8 admits a variable declaration with an inline enumerated type among a
// block's items, in a begin-end block and in a task body, and §6.19 makes the
// enumeration's members named constants of the block, which the declaration's
// own initializer and the statements after it read; the variable is of the
// enumeration, so §6.19.5's name() answers for it.
TEST(EnumerationSimulation, BlockInlineEnumVariableHasItsMembers) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  task tk;\n"
      "    enum {p, q} z;\n"
      "    z = q;\n"
      "    $display(\"%s %0d\", z.name(), z);\n"
      "  endtask\n"
      "  initial begin\n"
      "    automatic enum {r, s} y = s;\n"
      "    $display(\"%s %0d\", y.name(), r);\n"
      "    tk();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "s 0\nq 1\n");
}

// §6.19 with §7.4.1: an enumeration written with packed dimensions after its
// body is as wide as its base type, and its x member keeps the base's width,
// so name() finds the member whether a variable declares the enumeration,
// a typedef declares it with no variable of it, a typedef declares it and a
// variable is the array, or packed dimensions after a typedef name make the
// variable an array of the typedef's enumeration; at the array's width, the
// member's x bits outnumbered the constant's and no member matched (#7316).
TEST(EnumerationSimulation, XMemberOfAnEnumArrayIsNamedAtItsBaseWidth) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  enum logic [1:0] {A, X = 'x} [1:0] v;\n"
      "  typedef enum logic [1:0] {P, Y = 'x} [1:0] e_t;\n"
      "  typedef enum logic [1:0] {R, Z = 'x} [2:0] f_t;\n"
      "  f_t q;\n"
      "  typedef enum logic [1:0] {G, W = 'x} g_t;\n"
      "  g_t [1:0] s;\n"
      "  initial begin\n"
      "    $display(\"[%s] [%s] [%s] [%s] %b\", X.name(), Y.name(), Z.name(),\n"
      "             W.name(), Y);\n"
      "    $display(\"%0d %0d %0d\", $bits(v), $bits(q), $bits(s));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[X] [Y] [Z] [W] xx\n4 6 4\n");
}

// §6.19 with §23.9: a block's enumeration written with packed dimensions after
// its body declares constants as wide as its base type, while a variable of
// the typedef, or of the inline enumeration, is the whole packed array of it
// (#7316). A variable of an inline enumeration with a base range and no
// dimensions after the body is as wide as that range.
TEST(EnumerationSimulation, BlockEnumArrayConstantsAreAsWideAsItsBase) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    typedef enum bit [1:0] {A, B, C} [1:0] e_t;\n"
      "    e_t x;\n"
      "    enum logic [2:0] {P, Q} [1:0] w;\n"
      "    enum logic [2:0] {R, S} y;\n"
      "    $display(\"%b %b %0d %0d %0d\", C, Q, $bits(x), $bits(w),\n"
      "             $bits(y));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "10 001 4 6 3\n");
}

// §6.19 with §26.3: a package's enumeration written with packed dimensions
// after its body, by a data declaration or a typedef, declares constants as
// wide as its base type, which pk::B reads (#7316).
TEST(EnumerationSimulation, PackageEnumArrayConstantsAreAsWideAsItsBase) {
  SimFixture f;
  auto out = RunCapture(
      "package pk;\n"
      "  enum bit [1:0] {A, B} [2:0] v;\n"
      "  typedef enum logic [2:0] {P, Q} [1:0] e_t;\n"
      "endpackage\n"
      "module t;\n"
      "  initial $display(\"%b %b\", pk::B, pk::Q);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "01 001\n");
}

// §6.19: an enumeration's base type, and the width that base gives it: int
// where none is written, each integer atom type by its own width, each scalar
// integer vector type as one bit, and a vector by its dimension. A base that
// is a typedef name is issue #11449.
struct EnumBase {
  const char* base;
  uint32_t width;
};

constexpr std::array kEnumBases = {
    EnumBase{"", 32},
    EnumBase{"byte", 8},
    EnumBase{"byte unsigned", 8},
    EnumBase{"shortint", 16},
    EnumBase{"int", 32},
    EnumBase{"int unsigned", 32},
    EnumBase{"longint", 64},
    EnumBase{"integer", 32},
    EnumBase{"time", 64},
    EnumBase{"bit", 1},
    EnumBase{"logic", 1},
    EnumBase{"reg unsigned", 1},
    EnumBase{"bit [11:0]", 12},
    EnumBase{"logic signed [2:0]", 3},
};

// A design declaring an enumeration of `base` in each place of a module one
// may stand -- a module's typedef and a variable of it, a module's variable of
// an inline enumeration, a package's typedef, the compilation unit's typedef,
// a generate block's typedef, a variable of an inline enumeration local to an
// initial procedure and to a function, and a packed structure member -- with
// r recording, bit by bit, whether each is `width` bits wide.
std::string EnumWidthDesign(const EnumBase& enum_base) {
  return std::format(
      "package p;\n"
      "  typedef enum {0} {{PA, PB}} e_t;\n"
      "endpackage\n"
      "typedef enum {0} {{UA, UB}} u_t;\n"
      "module t;\n"
      "  typedef enum {0} {{MA, MB}} m_t;\n"
      "  m_t mv;\n"
      "  enum {0} {{IA, IB}} iv;\n"
      "  p::e_t pv;\n"
      "  u_t uv;\n"
      "  typedef struct packed {{ m_t f; bit g; }} s_t;\n"
      "  localparam int kWidth = $bits(m_t);\n"
      "  bit [11:0] r;\n"
      "  if (1) begin : gb\n"
      "    typedef enum {0} {{GA, GB}} g_t;\n"
      "    g_t gv;\n"
      "    initial r[11] = $bits(gv) == {1} && $bits(g_t) == {1};\n"
      "  end\n"
      "  function automatic int local_width();\n"
      "    enum {0} {{FA, FB}} fv;\n"
      "    return $bits(fv);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    enum {0} {{LA, LB}} lv;\n"
      "    r[0] = $bits(mv) == {1};\n"
      "    r[1] = $bits(iv) == {1};\n"
      "    r[2] = $bits(pv) == {1};\n"
      "    r[3] = $bits(uv) == {1};\n"
      "    r[4] = $bits(m_t) == {1};\n"
      "    r[5] = $bits(p::e_t) == {1};\n"
      "    r[6] = $bits(u_t) == {1};\n"
      "    r[7] = $bits(s_t) == {1} + 1;\n"
      "    r[8] = kWidth == {1};\n"
      "    r[9] = $bits(lv) == {1};\n"
      "    r[10] = local_width() == {1};\n"
      "  end\n"
      "endmodule\n",
      enum_base.base, enum_base.width);
}

TEST(EnumerationSimulation, EnumerationIsAsWideAsItsBaseTypeEverywhere) {
  for (const EnumBase& enum_base : kEnumBases) {
    const std::string kSrc = EnumWidthDesign(enum_base);
    SCOPED_TRACE(kSrc);
    EXPECT_EQ(RunAndGet(kSrc, "r"), 0xFFFu);
  }
}

// The same enumerations in the remaining places one may stand: an interface's,
// a program's and a checker's typedef with a variable of it, and an inline
// enumeration's variable beside it, the checker setting its flag from an
// always_comb (§17.5); and a class's typedef with a property of it and a
// property of an inline enumeration, read through a handle. r records each.
std::string EnumWidthInOtherScopes(const EnumBase& enum_base) {
  const std::string kDeclared = std::format(
      "  typedef enum {0} {{XA, XB}} x_t;\n  x_t v;\n"
      "  enum {0} {{YA, YB}} w;\n",
      enum_base.base);
  const std::string kOk =
      std::format("$bits(v) == {0} && $bits(x_t) == {0} && $bits(w) == {0}",
                  enum_base.width);
  return std::format(
      "interface ifc;\n{0}  bit ok;\n  initial ok = {1};\nendinterface\n"
      "program pg;\n{0}  bit ok;\n"
      "  initial begin\n    ok = {1};\n    #2;\n  end\nendprogram\n"
      "checker ck;\n{0}  bit ok;\n  always_comb ok = {1};\nendchecker\n"
      "class c;\n{0}endclass\n"
      "module t;\n"
      "  ifc u_ifc();\n"
      "  pg u_pg();\n"
      "  ck u_ck();\n"
      "  bit [3:0] r;\n"
      "  c h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    #1;\n"
      "    r[0] = u_ifc.ok;\n"
      "    r[1] = u_pg.ok;\n"
      "    r[2] = u_ck.ok;\n"
      "    r[3] = $bits(h.v) == {2} && $bits(c::x_t) == {2} &&\n"
      "           $bits(h.w) == {2};\n"
      "  end\n"
      "endmodule\n",
      kDeclared, kOk, enum_base.width);
}

TEST(EnumerationSimulation, EnumerationIsAsWideAsItsBaseInEveryScope) {
  for (const EnumBase& enum_base : kEnumBases) {
    const std::string kSrc = EnumWidthInOtherScopes(enum_base);
    SCOPED_TRACE(kSrc);
    EXPECT_EQ(RunAndGet(kSrc, "r"), 0xFu);
  }
}

// §6.19 with §6.24.1: a variable of an enumeration holds its base type's bits
// and no more, so a value one bit wider cast to the enumeration and read back
// through an int keeps the base's width and signing: the low byte of 9'h1FF
// is -1 in a signed byte and 255 in an unsigned one.
TEST(EnumerationSimulation, EnumerationVariableHoldsItsBaseTypesBits) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef enum byte {A, B} sb_t;\n"
                      "  typedef enum byte unsigned {C, D} ub_t;\n"
                      "  typedef enum shortint {E, F} ss_t;\n"
                      "  typedef enum bit {G, H} b1_t;\n"
                      "  sb_t sb;\n"
                      "  ub_t ub;\n"
                      "  ss_t ss;\n"
                      "  b1_t b1;\n"
                      "  bit [3:0] r;\n"
                      "  initial begin\n"
                      "    sb = sb_t'(9'h1FF);\n"
                      "    ub = ub_t'(9'h1FF);\n"
                      "    ss = ss_t'(17'h1FFFF);\n"
                      "    b1 = b1_t'(2'b11);\n"
                      "    r[0] = int'(sb) == -1;\n"
                      "    r[1] = int'(ub) == 255;\n"
                      "    r[2] = int'(ss) == -1;\n"
                      "    r[3] = int'(b1) == 1;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xFu);
}

// §6.19 with §7.4.1: the packed dimensions written after an enumeration's
// body make a packed array of it, each element as wide as the base: a byte
// base, and a vector base whose own dimension is multiplied by the array's.
TEST(EnumerationSimulation, PackedArrayOfEnumerationsMultipliesItsBaseWidth) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef enum byte {A, B} [1:0] pb_t;\n"
                      "  typedef enum bit [5:0] {C, D} [2:0] pv_t;\n"
                      "  pb_t pb;\n"
                      "  pv_t pv;\n"
                      "  bit [3:0] r;\n"
                      "  initial begin\n"
                      "    r[0] = $bits(pb) == 16;\n"
                      "    r[1] = $bits(pb_t) == 16;\n"
                      "    r[2] = $bits(pv) == 18;\n"
                      "    r[3] = $bits(pv_t) == 18;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xFu);
}

// §6.19: a constant of an enumeration is a value of it, as wide as the base
// and signed where the base is, wherever the enumeration is declared: -1 of a
// byte base widens to -1 in an int, and 255 of an unsigned byte base widens to
// 255, read bare in the module, through a package's scope and through a
// class's.
TEST(EnumerationSimulation, ConstantOfAnEnumerationCarriesItsBasesSigning) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef enum byte {PM = -1, PN = 1} e_t;\n"
                      "  typedef enum byte unsigned {PU = 255} u_t;\n"
                      "endpackage\n"
                      "class c;\n"
                      "  typedef enum byte {CM = -1, CN = 1} e_t;\n"
                      "  typedef enum byte unsigned {CU = 255} u_t;\n"
                      "endclass\n"
                      "module t;\n"
                      "  typedef enum byte {MM = -1, MN = 1} e_t;\n"
                      "  typedef enum byte unsigned {MU = 255} u_t;\n"
                      "  int x;\n"
                      "  bit [5:0] r;\n"
                      "  initial begin\n"
                      "    x = MM;\n"
                      "    r[0] = x == -1;\n"
                      "    x = MU;\n"
                      "    r[1] = x == 255;\n"
                      "    x = p::PM;\n"
                      "    r[2] = x == -1;\n"
                      "    x = p::PU;\n"
                      "    r[3] = x == 255;\n"
                      "    x = c::CM;\n"
                      "    r[4] = x == -1;\n"
                      "    x = c::CU;\n"
                      "    r[5] = x == 255;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0x3Fu);
}

// §6.19 with §6.19.5: first(), last(), next() and prev() return values of the
// enumeration, as wide as its base and signed where the base is. So a
// variable of a byte enumeration holding its member -1 equals first() of
// itself, next() steps from that member and prev() steps back to it, and two
// results concatenate to
// the base's width each; an unsigned byte base's member 255 widens to 255.
TEST(EnumerationSimulation, EnumerationMethodsReturnValuesOfItsBase) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef enum byte {M = -1, N = 1} e_t;\n"
                      "  typedef enum byte unsigned {U = 255, V = 1} u_t;\n"
                      "  e_t e;\n"
                      "  e_t e2 = N;\n"
                      "  u_t u;\n"
                      "  int x;\n"
                      "  bit [15:0] c;\n"
                      "  bit [5:0] r;\n"
                      "  initial begin\n"
                      "    e = M;\n"
                      "    u = U;\n"
                      "    r[0] = e == e.first();\n"
                      "    r[1] = e.next() == N;\n"
                      "    r[2] = e2.prev() == M;\n"
                      "    x = e.first();\n"
                      "    r[3] = x == -1;\n"
                      "    x = u.first();\n"
                      "    r[4] = x == 255;\n"
                      "    c = {e.first(), e.last()};\n"
                      "    r[5] = c == 16'hFF01;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0x3Fu);
}

}  // namespace
