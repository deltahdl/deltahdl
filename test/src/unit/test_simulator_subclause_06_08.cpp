#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(VariableDeclaration, VariableCreation) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
}

TEST(VariableDeclaration, MultipleVariableCreation) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindVariable("a"), nullptr);
  EXPECT_NE(f.ctx.FindVariable("b"), nullptr);
  EXPECT_NE(f.ctx.FindVariable("c"), nullptr);
}

TEST(VariableDeclaration, Logic4StateDefaultInit) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("data");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

// Table 6-7 gives the default by type, and an element of an unpacked array is
// a variable of the array's element type, so a 4-state element left without a
// value defaults to 'x exactly as the scalar above does. Reading it as zero
// would make an element nobody wrote indistinguishable from one written 0.
TEST(VariableDeclaration, Logic4StateArrayElementDefaultInit) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:2];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

// Table 6-7 gives a scalar and an element of an array of the same type one
// default, so the two are the same value and the words holding them are equal
// word for word. The assertion deliberately carries no `& 0xFF`: the mask the
// two cases above use is the width of the declaration written into the
// assertion, and masking is what hid the two producers disagreeing about the
// bits above it -- the element's 'x came from MakeAllX, which filled every bit
// of the top word, and the scalar's from SimContext::CreateVariable, which
// masked. §11.4.5 is where the disagreement showed, `arr[0] === data` reading
// 0 for two values of the same declared type and the same default.
TEST(VariableDeclaration, ArrayElementDefaultXMatchesScalarDefaultX) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [7:0] arr [0:2];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* scalar = f.ctx.FindVariable("data");
  auto* element = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(scalar, nullptr);
  ASSERT_NE(element, nullptr);

  ASSERT_EQ(element->value.nwords, scalar->value.nwords);
  EXPECT_EQ(element->value.words[0].aval, scalar->value.words[0].aval);
  EXPECT_EQ(element->value.words[0].bval, scalar->value.words[0].bval);
}

// The 2-state half of the same rule, which is what keeps the fix from being a
// blanket switch to 'x: Table 6-7 gives a 2-state integral '0, so an element of
// a bit array left without a value stays zero.
TEST(VariableDeclaration, Bit2StateArrayElementDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] arr [0:2];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0u);
}

TEST(VariableDeclaration, Int2StateDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].aval, 0u);
}

TEST(VariableDeclaration, Bit2StateDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
}

TEST(VariableDeclaration, RealDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].aval, 0u);
}

TEST(VariableDeclaration, ShortrealDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortreal sr;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("sr");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, 0u);
}

TEST(VariableDeclaration, StaticInitializerAppliesBeforeInitialBlock) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x = 42;\n"
      "  int observed;\n"
      "  initial observed = x;\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 42u);
}

TEST(VariableDeclaration, ChandleDefaultIsNull) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle h;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("h");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

TEST(VariableDeclaration, StringDefaultIsRegisteredAsString) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  string s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(f.ctx.IsStringVariable("s"));
}

TEST(VariableDeclaration, EventDefaultIsNewEvent) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("e");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_event);
  EXPECT_FALSE(var->is_null_event);
}

TEST(VariableDeclaration, StaticInitializerWithBinaryExpression) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x = 10 * 4 + 2;\n"
      "  int observed;\n"
      "  initial observed = x;\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 42u);
}

TEST(VariableDeclaration, StaticInitializerReferencesEarlierStatic) {
  auto val = RunAndGet(
      "module t;\n"
      "  int base = 7;\n"
      "  int derived = base * 6;\n"
      "  int observed;\n"
      "  initial observed = derived;\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 42u);
}

TEST(VariableDeclaration, StaticInitializerWithClassNew) {
  auto val = RunAndGet(
      "class C;\n"
      "  int v;\n"
      "  function new(int initial_v);\n"
      "    v = initial_v;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C handle = new(42);\n"
      "  int observed;\n"
      "  initial observed = handle.v;\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 42u);
}

TEST(VariableDeclaration,
     EnumImplicitBaseDefaultsToBaseTypeZeroNotFirstMember) {
  // Table 6-7: an enumeration's default initial value is its base type's
  // default value, NOT its first enumerator. With no explicit base the base
  // type is int (2-state), whose default is 0 -- even though the first
  // enumerator here is 5. Observing 0 (rather than 5) exercises exactly this
  // rule.
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  enum { A = 5, B } e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("e");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

TEST(VariableDeclaration, Enum4StateBaseDefaultsToX) {
  // Table 6-7: an enumeration inherits its base type's default. A 4-state base
  // (logic) makes the default x, distinguishing it from a 2-state-base enum
  // whose default is 0. x is Convention A (aval=bval=1) per bit.
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  enum logic [1:0] { A, B } e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("e");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].bval & 0x3u, 0x3u);
}

TEST(VariableDeclaration, ClassHandleDefaultIsNull) {
  // Table 6-7: a class-handle variable with no initializer defaults to null,
  // encoded as an all-zero handle (aval=bval=0) -- the same null encoding used
  // for chandle.
  LowerFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int v;\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("h");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

TEST(VariableDeclaration, VariableStoresValueBetweenAssignmentAndRead) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x;\n"
      "  int observed;\n"
      "  initial begin\n"
      "    x = 99;\n"
      "    observed = x;\n"
      "  end\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 99u);
}

// §10.9.1 forbids an element no rule covers, so this declaration is reported at
// elaboration -- and the value the element ends up with still has to be one
// answer rather than two. The one-dimensional keyed maker gave a known 0 where
// the positional maker beside it and the multidimensional one both give §6.8's
// Table 6-7 default, so one spelling of an illegal pattern read 00 and the
// other read 'x.
TEST(VariableDeclaration, KeyedPatternUncoveredElementTakesTable67Default) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a [0:2] = '{int: 8'h05};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("a[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
}

// The run-time keyed writer answers the same question, and no elaboration rule
// reaches a pattern written as a statement, so this branch is reachable with no
// report at all -- which is why the two had to agree rather than one of them
// being unreachable.
TEST(VariableDeclaration, KeyedPatternStatementUncoveredElementTakesTable67) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a [0:2];\n"
      "  initial a = '{int: 8'h05};\n"
      "endmodule\n",
      f, "a[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
}

}  // namespace
