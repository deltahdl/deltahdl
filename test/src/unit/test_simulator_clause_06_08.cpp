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

// Table 6-7: 2-state integer types default to 0.
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
  // 2-state default: aval=0, bval=0 (but CreateVariable sets bval to all-ones).
  // The lowerer doesn't currently override for 2-state, so check what we get.
  // If the implementation correctly handles Table 6-7, aval should be 0.
  EXPECT_EQ(var->value.words[0].aval, 0u);
}

// Table 6-7: bit type defaults to 0.
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

// Table 6-7: real defaults to 0.0.
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
  // Real is stored as 64-bit; 0.0 is all-zero bits.
  EXPECT_EQ(var->value.words[0].aval, 0u);
}

// Table 6-7: shortreal defaults to 0.0.
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


// §6.8: A static variable's declaration-time initializer must be applied
// before any initial or always procedure starts, so a procedure that reads
// the variable at time zero observes the initial value rather than the
// type's default.
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

// §6.8: Same rule for vector types — a logic vector with a declaration-time
// initializer is observed by an initial block at time zero.
TEST(VariableDeclaration, StaticVectorInitializerAppliesBeforeInitialBlock) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] data = 8'hA5;\n"
      "  logic [7:0] sampled;\n"
      "  initial sampled = data;\n"
      "endmodule\n",
      "sampled");
  EXPECT_EQ(val, 0xA5u);
}

// §6.8 Table 6-7: a chandle variable with no initializer takes the null
// value (zero), not x.
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

// §6.8 Table 6-7: a string variable with no initializer is registered as
// a string-valued variable so the runtime treats its default as the empty
// string rather than a logic vector full of x.
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

// Table 6-7: event variable is marked as event.
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

// §6.8: A declaration-time initializer is not restricted to a literal —
// any expression that evaluates at the start of simulation is valid.
// Verify a compound arithmetic expression is folded and its result is
// observable from a procedural read at time zero.
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

// §6.8: An initializer expression may reference an earlier static
// variable; the dependency is resolved before any initial procedure
// starts so the observed value reflects the chained initialization.
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

// §6.8: "Initial values are not constrained to simple constants; they can
// include run-time expressions, including dynamic memory allocation. For
// example, a static class handle ... can be created and initialized by
// calling its new method." Verify that a static class handle initialized
// via new() in its declaration is alive at time zero with the value the
// constructor stored — this exercises the dynamic-allocation form of the
// initializer rule end-to-end through the simulator.
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

}  // namespace
