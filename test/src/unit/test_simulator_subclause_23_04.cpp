#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/diagnostic.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

void ExpectNestedOwnsNetAndOuterReadsZ(SimFixture& f, const char* nested_net) {
  auto* owned = f.ctx.FindVariable(nested_net);
  ASSERT_NE(owned, nullptr);
  EXPECT_EQ(owned->value.ToUint64(), 1u);

  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 1u);
}

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
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  module inner;\n"
      "    initial x = 8'd42;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  for (const Diagnostic& d : f.diag.Diagnostics()) {
    EXPECT_NE(d.severity, DiagSeverity::kError) << d.message;
  }
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("x");
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

  auto* nested_seen = f.ctx.FindVariable("nested_seen");
  ASSERT_NE(nested_seen, nullptr);
  EXPECT_EQ(nested_seen->value.ToUint64(), 42u);

  auto* seen = f.ctx.FindVariable("o1.seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_NE(seen->value.ToUint64(), 42u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'x'", 3,
                            "23.9"));
}

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

TEST(NestedModuleSimulation,
     InstanceAboveTheNestedDeclarationReadsRangedEnumConstants) {
  SimFixture f;
  ExpectOuterReadsThroughNestedAssign(
      f,
      "module top;\n"
      "  M m();\n"
      "  enum {C[2] = 5, D[1:2], E[3:1] = 9} e;\n"
      "  wire [7:0] v;\n"
      "  logic [7:0] r;\n"
      "  initial #1 r = v;\n"
      "  module M;\n"
      "    assign v = C1 + D2 + E1;\n"
      "  endmodule\n"
      "endmodule\n",
      25u);
}

TEST(NestedModuleSimulation,
     InstanceAboveTheNestedDeclarationReadsAStructMemberRangedEnumConstant) {
  SimFixture f;
  ExpectOuterReadsThroughNestedAssign(
      f,
      "module top;\n"
      "  M m();\n"
      "  typedef struct { enum {S[2] = 20} k; int n; } t;\n"
      "  wire [7:0] v;\n"
      "  logic [7:0] r;\n"
      "  initial #1 r = v;\n"
      "  module M;\n"
      "    assign v = S1;\n"
      "  endmodule\n"
      "endmodule\n",
      21u);
}

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

TEST(NestedModuleSimulation, NestedDeclarationReadsItsEnclosingInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(parameter int P = 0);\n"
                       "  int v = P;\n"
                       "  module inner;\n"
                       "    initial #P $display(\"v=%0d\", v);\n"
                       "  endmodule\n"
                       "endmodule\n"
                       "module top;\n"
                       "  int v = 9;\n"
                       "  m #(5) u();\n"
                       "  m #(6) w();\n"
                       "endmodule\n",
                       f),
            "v=5\nv=6\n");
}

}  // namespace
