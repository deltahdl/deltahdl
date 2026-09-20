#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The reading §6.10 gives a nested module's own implicit net: `nested_net`
// holds the 1 the nested assignment drove, and the outer net it never reached
// leaves r at z.
void ExpectNestedOwnsNetAndOuterReadsZ(SimFixture& f, const char* nested_net) {
  auto* owned = f.ctx.FindVariable(nested_net);
  ASSERT_NE(owned, nullptr);
  EXPECT_EQ(owned->value.ToUint64(), 1u);

  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 1u);
}

// The reading §23.4 with §6.10 gives a nested declaration whose instance is
// written above it: the outer name declared between the instance and the
// declaration stands above the declaration's text, so the nested module's
// reference resolves to it. `src` must elaborate with no report, and the
// outer r, which reads the object the nested module drove, holds `expected`.
void ExpectOuterReadsThroughNestedAssign(SimFixture& f, const char* src,
                                         uint64_t expected) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), expected);
}

TEST(NestedModuleSimulation, OuterScopeVariableAccessibleFromNestedModule) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  module inner;\n"
      "    initial x = 8'd42;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(NestedModuleSimulation, LocalNameShadowsOuterInSimulation) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd10;\n"
      "  module inner;\n"
      "    logic [7:0] x;\n"
      "    initial x = 8'd99;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 10u);
}

TEST(NestedModuleSimulation, PortlessNestedModuleInitialBlockRuns) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  module inner;\n"
      "    initial x = 8'd77;\n"
      "  endmodule\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 77u);
}

TEST(NestedModuleSimulation, PortedNestedModuleNotInstantiatedDoesNotRun) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd10;\n"
      "  module inner(input a);\n"
      "    initial x = 8'd99;\n"
      "  endmodule\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 10u);
}

// §23.4: the outer name space is visible to the inner module, so a nested
// module may *read* an outer-scope name as well as write one. The outer x is
// set at time 0; one tick later the nested module reads it and copies it into
// the outer y. Observing y == 5 proves the inner module resolved x to the
// enclosing scope's variable.
TEST(NestedModuleSimulation, OuterScopeVariableReadFromNestedModule) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] y;\n"
      "  initial x = 8'd5;\n"
      "  module inner;\n"
      "    initial #1 y = x;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 5u);
}

// §23.4: "The outer name space is visible to the inner module so that any name
// declared there can be used, unless hidden by a local name, provided the
// module is declared and instantiated in the same scope." That visibility is
// what tells a nested declaration apart from a module declared elsewhere and
// merely instantiated, which §23.9 stops at the module boundary. The cases
// above establish the visibility itself; this one establishes that it belongs
// to the nested declaration rather than to instantiation in general, by
// declaring `outer` at the top level and instantiating it beside a nested
// `inner` that reads the same name. Only the nested one may read `x`, so the
// two answers must differ, and asserting them together is what stops a change
// to either rule from silently taking the other with it.
TEST(NestedModuleSimulation, OuterNameIsVisibleToANestedDeclarationOnly) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module outer;\n"
      "  logic [7:0] seen;\n"
      "  initial #1 seen = x;\n"
      "endmodule\n"
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] nested_seen;\n"
      "  initial x = 8'd42;\n"
      "  module inner;\n"
      "    initial #1 nested_seen = x;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "  outer o1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  // The nested declaration reads the enclosing module's x.
  auto* nested_seen = f.ctx.FindVariable("nested_seen");
  ASSERT_NE(nested_seen, nullptr);
  EXPECT_EQ(nested_seen->value.ToUint64(), 42u);

  // The separately declared module does not: its own scope declares no x, and
  // §23.9 stops the search for a variable at its module boundary.
  auto* seen = f.ctx.FindVariable("o1.seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_NE(seen->value.ToUint64(), 42u);
}

// §23.4 with §23.3: a nested declaration is a module, and each instantiation
// of it is a separate instance whose own declarations -- the `wire q2` of
// the clause's ff2, encapsulated in it -- belong to that instance alone, as
// §36.10 spells out for m1.w and m2.w of any module instantiated twice. The
// outer name space being visible does not make a net the nested module
// declares for itself the enclosing module's. Two instances of a nested M
// each drive their own w from their own input; the top reads x*10 + y = 10,
// and m1.w holds 1 beside m2.w holding 0. With no net created under either
// instance, neither assignment found a target, both m1.w and m2.w were
// absent, and x and y were never driven.
TEST(NestedModuleSimulation, EachInstanceOfANestedDeclarationOwnsItsNets) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic a, b;\n"
      "  logic [7:0] r;\n"
      "  wire x, y;\n"
      "  module M(input logic i, output wire o);\n"
      "    wire w;\n"
      "    assign w = i;\n"
      "    assign o = w;\n"
      "  endmodule\n"
      "  M m1(.i(a), .o(x));\n"
      "  M m2(.i(b), .o(y));\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 0;\n"
      "    #1 r = x * 10 + y;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 10u);

  auto* m1_w = f.ctx.FindVariable("m1.w");
  ASSERT_NE(m1_w, nullptr);
  EXPECT_EQ(m1_w->value.ToUint64(), 1u);

  auto* m2_w = f.ctx.FindVariable("m2.w");
  ASSERT_NE(m2_w, nullptr);
  EXPECT_EQ(m2_w->value.ToUint64(), 0u);
}

// §23.4 with §6.10: an implicit net belongs to the scope the reference that
// declares it appears in, and a nested module is such a scope, so a name a
// continuous assignment inside it writes that no enclosing module declares is
// the nested module's own implicit net -- one per instance, as §36.10 has for
// any net of a module instantiated twice -- and not an outer name §23.4 makes
// visible. Two instances of M each drive their own q and hand it out through
// o; the top reads x*10 + y = 11 and finds m1.q and m2.q each holding 1. With
// every implicit net of a nested declaration left to the outer scope, neither
// m1.q nor m2.q was made, and o was driven from nothing.
TEST(NestedModuleSimulation, NestedDeclarationOwnsAnUndeclaredImplicitNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] r;\n"
      "  wire x, y;\n"
      "  module M(output o);\n"
      "    assign q = 1'b1;\n"
      "    assign o = q;\n"
      "  endmodule\n"
      "  M m1(.o(x));\n"
      "  M m2(.o(y));\n"
      "  initial #1 r = x * 10 + y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 11u);

  auto* m1_q = f.ctx.FindVariable("m1.q");
  ASSERT_NE(m1_q, nullptr);
  EXPECT_EQ(m1_q->value.ToUint64(), 1u);

  auto* m2_q = f.ctx.FindVariable("m2.q");
  ASSERT_NE(m2_q, nullptr);
  EXPECT_EQ(m2_q->value.ToUint64(), 1u);
}

// §23.4: the outer name space is visible to the nested module, so a
// continuous assignment inside it to a name the enclosing module declares
// drives that outer net, and no net of the name is made under the instance,
// which would shadow the outer one and take the assignment with it. The top's
// w reads 1 through the nested assignment, and "m.w" is absent. This holds the
// case apart from the one above: there the name is declared nowhere and is
// the instance's own.
TEST(NestedModuleSimulation, NestedDeclarationDrivesAnOuterNetInPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire w;\n"
      "  logic r;\n"
      "  module M;\n"
      "    assign w = 1'b1;\n"
      "  endmodule\n"
      "  M m();\n"
      "  initial #1 r = w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("m.w"), nullptr);
}

// §23.4 with §6.10: the outer name space is visible to the nested module, but
// §6.10 gives an identifier on the left of a continuous assignment an implicit
// net of the assignment's own scope unless it was declared previously in that
// scope or in one it can directly reference, and "previously" is the text
// above the assignment. An outer w declared below M's text -- here below the
// instance as well -- is not that, so M drives an implicit w of its own under
// the instance and the outer w has no driver: "m.w" holds 1 and r reads z.
// With the outer declaration taken for M's regardless of order, r read 1 and
// "m.w" was absent, which is the answer only when `wire w` stands above M.
TEST(NestedModuleSimulation,
     NestedDeclarationOwnsANetTheOuterModuleDeclaresBelowIt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  module M;\n"
      "    assign w = 1'b1;\n"
      "  endmodule\n"
      "  M m();\n"
      "  wire w;\n"
      "  logic r;\n"
      "  initial #1 r = w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  ExpectNestedOwnsNetAndOuterReadsZ(f, "m.w");
}

// §6.10 measures "previously" from the assignment's text, which stands inside
// M's declaration, not from the instance below it. An outer w declared between
// M's endmodule and `M m()` is therefore still declared after the assignment,
// and the answer is the one above: "m.w" holds 1 and r reads z. The names
// visible to M were taken where the instance stood, so w was among them, r
// read 1 and "m.w" was absent.
TEST(NestedModuleSimulation,
     OuterNetDeclaredBetweenNestedDeclarationAndInstanceIsNotTheNestedOnes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  module M;\n"
      "    assign w = 1'b1;\n"
      "  endmodule\n"
      "  wire w;\n"
      "  M m();\n"
      "  logic r;\n"
      "  initial #1 r = w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  ExpectNestedOwnsNetAndOuterReadsZ(f, "m.w");
}

// §6.10 measures "previously" from the assignment's text, which stands in M's
// declaration, wherever M's instance is written. With `M m()` above the
// declaration and the outer w between the two, w is declared above M's text,
// so M's assignment drives the outer w in place: r reads 1 and no net is made
// under m. The names visible to M were taken where the instance stood, above
// w, so M drove an implicit w of its own, "m.w" held 1 and r read z.
TEST(NestedModuleSimulation,
     InstanceAboveTheNestedDeclarationDrivesAnOuterNetDeclaredBetweenThem) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  M m();\n"
      "  wire w;\n"
      "  logic r;\n"
      "  initial #1 r = w;\n"
      "  module M;\n"
      "    assign w = 1'b1;\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(f.ctx.FindVariable("m.w"), nullptr);
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

// §6.19 declares an enumeration's literals as named constants of the scope
// holding the enumeration, so top's `enum {A = 5, B} e` declares B in top,
// and §6.10's "previously" is measured from M's text, below the enumeration
// wherever `M m()` stands. M's assignment reads top's B, 6, into the outer v,
// and r reads 6. The names counted above the declaration were the items'
// own names alone, so B was not among them, and M's read of B was reported
// an undeclared identifier under §23.9.
TEST(NestedModuleSimulation,
     InstanceAboveTheNestedDeclarationReadsAnEnumConstantDeclaredBetweenThem) {
  SimFixture f;
  ExpectOuterReadsThroughNestedAssign(f,
                                      "module top;\n"
                                      "  M m();\n"
                                      "  enum {A = 5, B} e;\n"
                                      "  wire [7:0] v;\n"
                                      "  logic [7:0] r;\n"
                                      "  initial #1 r = v;\n"
                                      "  module M;\n"
                                      "    assign v = B;\n"
                                      "  endmodule\n"
                                      "endmodule\n",
                                      6u);
}

// §6.19 with §7.2 and §23.9: an enumeration written as the type of a
// structure member declares its literals where the structure is written, a
// structure being no scope of its own, so top's typedef declares Q in top as
// the bare enumeration above declares B, and M reads Q, 4, the same way.
TEST(NestedModuleSimulation,
     InstanceAboveTheNestedDeclarationReadsAStructMemberEnumConstant) {
  SimFixture f;
  ExpectOuterReadsThroughNestedAssign(
      f,
      "module top;\n"
      "  M m();\n"
      "  typedef struct { enum {P = 3, Q} k; int n; } t;\n"
      "  wire [7:0] v;\n"
      "  logic [7:0] r;\n"
      "  initial #1 r = v;\n"
      "  module M;\n"
      "    assign v = Q;\n"
      "  endmodule\n"
      "endmodule\n",
      4u);
}

// §6.10 gives an undeclared identifier on the left of a continuous assignment
// an implicit net of the scope the assignment appears in, so top's `assign q
// = 1'bz` declares q in top, above M's text. M's `assign q = 1'b1` drives that
// outer q rather than an implicit q of its own: no net is made under m, and
// r reads 1, the z driver deferring to the driven value (§6.6.1). The names
// counted above the declaration were the items' own names alone, so q was
// not among them, "m.q" held 1 and r read z.
TEST(NestedModuleSimulation,
     InstanceAboveTheNestedDeclarationDrivesAnOuterImplicitNetDeclaredBetween) {
  SimFixture f;
  ExpectOuterReadsThroughNestedAssign(f,
                                      "module top;\n"
                                      "  M m();\n"
                                      "  assign q = 1'bz;\n"
                                      "  logic r;\n"
                                      "  initial #1 r = q;\n"
                                      "  module M;\n"
                                      "    assign q = 1'b1;\n"
                                      "  endmodule\n"
                                      "endmodule\n",
                                      1u);
  EXPECT_EQ(f.ctx.FindVariable("m.q"), nullptr);
}

// §23.4 applied twice: B is declared and instantiated in A, which is declared
// and instantiated in top, so top's name space is visible in B through A's,
// and a v top declares above A is driven in place by B's assignment. r reads
// 1 and no net is made under a.b.
TEST(NestedModuleSimulation,
     DoublyNestedDeclarationDrivesTheOutermostNetInPlace) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire v;\n"
      "  logic r;\n"
      "  module A;\n"
      "    module B;\n"
      "      assign v = 1'b1;\n"
      "    endmodule\n"
      "    B b();\n"
      "  endmodule\n"
      "  A a();\n"
      "  initial #1 r = v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("a.b.v"), nullptr);
}

// The same two levels with top's v declared below A: §6.10's "previously"
// fails at both levels, so B owns an implicit v under a.b holding 1 and top's
// v is undriven, r reading z.
TEST(NestedModuleSimulation, DoublyNestedDeclarationOwnsANetDeclaredBelowIt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  module A;\n"
      "    module B;\n"
      "      assign v = 1'b1;\n"
      "    endmodule\n"
      "    B b();\n"
      "  endmodule\n"
      "  A a();\n"
      "  wire v;\n"
      "  logic r;\n"
      "  initial #1 r = v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  ExpectNestedOwnsNetAndOuterReadsZ(f, "a.b.v");
}

}  // namespace
