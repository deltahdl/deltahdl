#include <gtest/gtest.h>

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

// §6.19: "An enumerated type declares a set of integral named constants", and
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

}  // namespace
