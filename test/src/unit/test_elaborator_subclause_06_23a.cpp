#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TypeOperatorSim, TypeOpInt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 42;\n"
      "    b = 99;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 99u);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpLogic) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_FALSE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpByte) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 8'hCD;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpShortint) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 16'h1234;\n"
      "    b = 16'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpLongint) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  longint a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 64'hDEAD_BEEF_CAFE_BABE;\n"
      "    b = 64'h0123_4567_89AB_CDEF;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
  EXPECT_EQ(var->value.ToUint64(), 0x0123456789ABCDEFu);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpInteger) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 32'hDEAD;\n"
      "    b = 32'hBEEF;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xBEEFu);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpReal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 3.14;\n"
      "    b = 2.71;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
}

TEST(TypeOperatorSim, TypeOpPreservesSignedInt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a;\n"
      "  var type(a) result;\n"
      "  initial result = -1;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_signed);

  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

TEST(TypeOperatorSim, TypeOpWidthTruncation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  initial result = 32'hFFFF;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);

  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

static void LowerRunAndCompareWidths(SimFixture& f, RtlirDesign* design,
                                     Variable*& va_out, Variable*& vb_out) {
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  va_out = f.ctx.FindVariable("a");
  vb_out = f.ctx.FindVariable("b");
  ASSERT_NE(va_out, nullptr);
  ASSERT_NE(vb_out, nullptr);
  EXPECT_EQ(va_out->value.width, vb_out->value.width);
}

TEST(TypeOperatorSim, TypeOpIntDifferentValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 1000;\n"
      "    b = 2000;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Variable* va = nullptr;
  Variable* vb = nullptr;
  LowerRunAndCompareWidths(f, design, va, vb);
  EXPECT_EQ(va->value.ToUint64(), 1000u);
  EXPECT_EQ(vb->value.ToUint64(), 2000u);
}

TEST(TypeOperatorSim, TypeOpShortintSignExtension) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) result;\n"
      "  int wide;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    result = a;\n"
      "    wide = result;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_TRUE(var->is_signed);

  EXPECT_EQ(var->value.ToUint64(), 0xFFFFu);
}

TEST(TypeOperatorSim, TypeOpParameterTypeDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter type T = int;\n"
      "  T x;\n"
      "  var type(x) result;\n"
      "  initial begin\n"
      "    x = 42;\n"
      "    result = 77;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(TypeOperatorSim, TypeOpEnumType) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  var type(c) result;\n"
      "  initial begin\n"
      "    c = GREEN;\n"
      "    result = 2;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(TypeOperatorSim, TypeOpIntOverflow) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a;\n"
      "  var type(a) result;\n"
      "  initial result = 64'hFFFF_FFFF_1234_5678;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);

  EXPECT_EQ(var->value.ToUint64(), 0x12345678u);
}

TEST(TypeOperatorSim, TypeOpMatchingWidths) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Variable* va = nullptr;
  Variable* vb = nullptr;
  LowerRunAndCompareWidths(f, design, va, vb);
  EXPECT_EQ(va->is_signed, vb->is_signed);
}

TEST(TypeOperatorSim, TypeOpLongintMaxValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  longint a;\n"
      "  var type(a) result;\n"
      "  initial result = 64'h7FFF_FFFF_FFFF_FFFF;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
  EXPECT_EQ(var->value.ToUint64(), 0x7FFFFFFFFFFFFFFFu);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpShortintZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) result;\n"
      "  initial result = 0;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpByteArithmeticSigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  initial begin\n"
      "    a = 100;\n"
      "    result = a + 8'd55;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_TRUE(var->is_signed);

  EXPECT_EQ(var->value.ToUint64(), 155u);
}

TEST(TypeOperatorSim, TypeOpChainedTypeRef) {
  SimFixture f;
  auto* vc = RunAndFindVar(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  var type(b) c;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b = 20;\n"
      "    c = 30;\n"
      "  end\n"
      "endmodule\n",
      f, "c");
  ASSERT_NE(vc, nullptr);
  EXPECT_EQ(vc->value.width, 32u);
  EXPECT_EQ(vc->value.ToUint64(), 30u);
  EXPECT_TRUE(vc->is_signed);
}

TEST(TypeOperatorSim, TypeOpMultipleAssignments) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a;\n"
      "  var type(a) result;\n"
      "  initial begin\n"
      "    result = 1;\n"
      "    result = 2;\n"
      "    result = 3;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(TypeOperatorSim, TypeOpShortintMaxUnsigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) result;\n"
      "  initial result = 16'hFFFF;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFu);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpByteFromWiderAssignment) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  int wide;\n"
      "  initial begin\n"
      "    wide = 32'h12345678;\n"
      "    result = wide;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);

  EXPECT_EQ(var->value.ToUint64(), 0x78u);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpLocalparamType) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam type T = type(int);\n"
      "  T x;\n"
      "  initial x = 55;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 55u);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpLogicVector) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 16'hBEEF;\n"
      "    b = 16'hCAFE;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

TEST(TypeOperatorSim, TypeOpWireNetDecl) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [7:0] x;\n"
      "  wire type(x) y;\n"
      "  assign x = 8'hAB;\n"
      "  assign y = 8'hCD;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(TypeOperatorSim, TypeOpSelfDeterminedBinaryWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte a;\n"
      "  int b;\n"
      "  var type(a + b) c;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "    c = 32'hDEAD_BEEF;\n"
      "  end\n"
      "endmodule\n",
      f, "c");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(TypeOperatorSim, TypeOpBitTypeUnsigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'hAB;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_FALSE(var->is_signed);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// §6.23 — the type operator applied to an expression yields that expression's
// self-determined type. Here the operand's type is produced by a user-defined
// typedef (§6.18) built from real source syntax: `bus_t` names a 24-bit logic
// vector, so `type(x)` derives a 24-bit unsigned type for the dependent
// declaration. Driven through the full pipeline and observed at runtime.
TEST(TypeOperatorSim, TypeOpTypedefVectorType) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef logic [23:0] bus_t;\n"
      "  bus_t x;\n"
      "  var type(x) y;\n"
      "  initial begin\n"
      "    x = 24'h123456;\n"
      "    y = 24'hABCDEF;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 24u);
  EXPECT_FALSE(var->is_signed);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDEFu);
}

// §6.23 has a type reference to a data type stand for that type. The parse
// reads `int`, a typedef name and a type parameter's name as identifiers, and
// none names a variable or a net here, so each is resolved as the type it
// spells.
TEST(TypeOperatorSim, TypeOfADataTypeOrATypedefIsThatType) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  parameter type T = logic [5:0];\n"
      "  var type(int) a;\n"
      "  var type(byte_t) c;\n"
      "  var type(T) g;\n"
      "  initial begin\n"
      "    a = -3;\n"
      "    c = 8'hA5;\n"
      "    g = 6'h2A;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.width, 32u);
  EXPECT_TRUE(a->is_signed);
  EXPECT_EQ(a->value.ToUint64(), 0xFFFFFFFDu);
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.width, 8u);
  EXPECT_EQ(c->value.ToUint64(), 0xA5u);
  auto* g = f.ctx.FindVariable("g");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->value.width, 6u);
  EXPECT_EQ(g->value.ToUint64(), 0x2Au);
}

// A type reference to a parameter stands for the parameter's type: the type
// it was declared with, `int` for P, or, declared with no type, the logic
// vector of its declared range or of its final value (§6.20.2): 12 bits for
// Q, 8 for U and 4 for the parameter port V. An expression over a parameter
// takes the parameter's width and signing, as one over a variable takes the
// variable's.
TEST(TypeOperatorSim, TypeOfAParameterIsTheParametersType) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module t #(parameter V = 4'h9);\n"
      "  parameter int P = 5;\n"
      "  parameter [11:0] Q = 1;\n"
      "  parameter U = 8'hA5;\n"
      "  var type(P) b;\n"
      "  var type(Q) d;\n"
      "  var type(-P) e;\n"
      "  var type(U) u;\n"
      "  var type(V) w;\n"
      "  initial begin\n"
      "    b = -3;\n"
      "    d = 12'hFFF;\n"
      "    e = -3;\n"
      "    u = 9'h1FF;\n"
      "    w = 5'h1F;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.width, 32u);
  EXPECT_TRUE(b->is_signed);
  EXPECT_EQ(b->value.ToUint64(), 0xFFFFFFFDu);
  auto* d = f.ctx.FindVariable("d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->value.width, 12u);
  EXPECT_FALSE(d->is_signed);
  EXPECT_EQ(d->value.ToUint64(), 0xFFFu);
  auto* e = f.ctx.FindVariable("e");
  ASSERT_NE(e, nullptr);
  EXPECT_EQ(e->value.width, 32u);
  EXPECT_TRUE(e->is_signed);
  auto* u = f.ctx.FindVariable("u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->value.width, 8u);
  EXPECT_EQ(u->value.ToUint64(), 0xFFu);
  auto* w = f.ctx.FindVariable("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->value.width, 4u);
  EXPECT_EQ(w->value.ToUint64(), 0xFu);
}

// §6.19.3 makes a typedef's enumeration a data type its named constants are
// of, and §6.23 has a type reference to one of them stand for that type, so
// `type(A)` declares v of e_t: four bits, holding B's 4'h4 whole.
TEST(TypeOperatorSim, TypeOfANamedEnumerationsConstantIsTheEnumeration) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef enum bit [3:0] {A = 4'h3, B} e_t;\n"
      "  var type(A) v;\n"
      "  initial v = B;\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.width, 4u);
  EXPECT_EQ(v->value.ToUint64(), 4u);
}

// A constant of an enumeration written as a variable's type, with no typedef
// to name it, stands for that enumeration all the same (§6.19.3): z is of w's
// type, 32 bits signed as `int`, the default base type (§6.19), makes it, and
// holds Y.
TEST(TypeOperatorSim, TypeOfAnAnonymousEnumerationsConstantIsTheEnumeration) {
  SimFixture f;
  auto* z = RunAndFindVar(
      "module t;\n"
      "  enum {X, Y} w;\n"
      "  var type(X) z;\n"
      "  initial z = Y;\n"
      "endmodule\n",
      f, "z");
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(z->value.width, 32u);
  EXPECT_TRUE(z->is_signed);
  EXPECT_EQ(z->value.ToUint64(), 1u);
}

// §6.19.3 checks an assignment to a variable of an enumerated type strictly,
// and a variable a type reference to one of the enumeration's constants
// declares is of that type: Y stands, and the integer 5 needs a cast.
TEST(TypeOperatorSim, AVariableOfAnAnonymousEnumerationsConstantsTypeIsStrict) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  enum {X, Y} w;\n"
      "  var type(X) z;\n"
      "  initial begin\n"
      "    z = Y;\n"
      "    z = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

// §6.19 with §7.2 declares the constants of an enumeration written as a
// structure member's type in the scope holding the structure, so P is the
// module's, and type(P) stands for the member's two-bit enumeration.
TEST(TypeOperatorSim, TypeOfAMemberEnumerationsConstantIsTheEnumeration) {
  SimFixture f;
  auto* z = RunAndFindVar(
      "module t;\n"
      "  struct packed { enum bit [1:0] {P, Q} f; bit k; } s;\n"
      "  var type(P) z;\n"
      "  initial z = Q;\n"
      "endmodule\n",
      f, "z");
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(z->value.width, 2u);
  EXPECT_EQ(z->value.ToUint64(), 1u);
}

// §26.3 makes a package's declarations visible in a module that imports them,
// by name or by a wildcard, and reachable through the package's scope; §3.12.1
// makes the compilation unit's declarations before the module visible in it.
// A type reference to any of these values stands for the value's type: pv's
// six bits, W's `int` both imported and written p::W, g's three bits, QV's
// ten through q's explicit import, and for the untyped U and R the eight bits
// of U's value and R's declared [3:0] (§6.20.2).
TEST(TypeOperatorSim, TypeOfAValueOfAPackageOrTheUnitIsItsType) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "package p;\n"
      "  parameter int W = 8;\n"
      "  parameter U = 8'hA5;\n"
      "  parameter [3:0] R = 1;\n"
      "  logic [5:0] pv;\n"
      "endpackage\n"
      "package q;\n"
      "  logic [9:0] QV;\n"
      "endpackage\n"
      "logic [2:0] g;\n"
      "module t;\n"
      "  import q::QV;\n"
      "  import p::*;\n"
      "  var type(pv) a;\n"
      "  var type(W) b;\n"
      "  var type(p::W) c;\n"
      "  var type(g) d;\n"
      "  var type(QV) e;\n"
      "  var type(U) u;\n"
      "  var type(R) h;\n"
      "  initial begin\n"
      "    a = 6'h3F;\n"
      "    b = -3;\n"
      "    c = -3;\n"
      "    d = 3'h5;\n"
      "    e = 10'h3FF;\n"
      "    u = 9'h1FF;\n"
      "    h = 5'h1F;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.width, 6u);
  EXPECT_EQ(a->value.ToUint64(), 0x3Fu);
  for (const char* name : {"b", "c"}) {
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->value.width, 32u) << name;
    EXPECT_TRUE(v->is_signed) << name;
    EXPECT_EQ(v->value.ToUint64(), 0xFFFFFFFDu) << name;
  }
  auto* d = f.ctx.FindVariable("d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->value.width, 3u);
  EXPECT_EQ(d->value.ToUint64(), 5u);
  auto* e = f.ctx.FindVariable("e");
  ASSERT_NE(e, nullptr);
  EXPECT_EQ(e->value.width, 10u);
  EXPECT_EQ(e->value.ToUint64(), 0x3FFu);
  auto* u = f.ctx.FindVariable("u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->value.width, 8u);
  EXPECT_EQ(u->value.ToUint64(), 0xFFu);
  auto* h = f.ctx.FindVariable("h");
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(h->value.width, 4u);
  EXPECT_EQ(h->value.ToUint64(), 0xFu);
}

// §6.23 with §26.3 and §7.2 — a member of a structure variable a package
// declares, `pkg::v.f`, names no scope, so it is no hierarchical reference.
TEST(TypeOperatorElab, PackageStructureMemberInTypeArgAccepted) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef struct packed { bit [7:0] f; bit g; } st;\n"
             "  st v;\n"
             "endpackage\n"
             "module m;\n"
             "  int d;\n"
             "  initial d = type(pkg::v.f)'(5);\n"
             "endmodule\n"));
}

}  // namespace
