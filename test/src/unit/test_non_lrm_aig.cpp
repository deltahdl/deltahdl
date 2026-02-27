// §non-lrm:aig

#include <gtest/gtest.h>

#include "synthesis/aig.h"
#include "synthesis/aig_opt.h"
#include "fixture_synthesizer.h"

using namespace delta;

namespace {

TEST(Aig, StructuralHashingDeduplication) {
  AigGraph graph;
  auto a = graph.AddInput();
  auto b = graph.AddInput();
  auto c1 = graph.AddAnd(a, b);
  auto c2 = graph.AddAnd(a, b);
  EXPECT_EQ(c1, c2);
}

TEST(Aig, AddOutput) {
  AigGraph graph;
  auto a = graph.AddInput();
  graph.AddOutput(a);
  ASSERT_EQ(graph.outputs.size(), 1);
  EXPECT_EQ(graph.outputs[0], a);
}

TEST(Aig, XorConstruction) {
  AigGraph graph;
  auto a = graph.AddInput();
  auto b = graph.AddInput();
  auto x = graph.AddXor(a, b);
  EXPECT_GT(AigVar(x), 0);
}

TEST(Aig, MuxConstruction) {
  AigGraph graph;
  auto s = graph.AddInput();
  auto a = graph.AddInput();
  auto b = graph.AddInput();
  auto m = graph.AddMux(s, a, b);
  EXPECT_GT(AigVar(m), 0);
}

TEST(Aig, LiteralHelpers) {
  for (uint32_t id = 0; id < 10; ++id) {
    auto lit = AigLit(id, false);
    EXPECT_EQ(AigVar(lit), id);
    EXPECT_FALSE(AigIsCompl(lit));

    auto lit_c = AigLit(id, true);
    EXPECT_EQ(AigVar(lit_c), id);
    EXPECT_TRUE(AigIsCompl(lit_c));
  }
}

TEST(Aig, AddInput) {
  AigGraph graph;
  auto a = graph.AddInput();
  auto b = graph.AddInput();
  EXPECT_EQ(graph.inputs.size(), 2);
  EXPECT_NE(AigVar(a), AigVar(b));
}

TEST(Aig, AddAnd) {
  AigGraph graph;
  auto a = graph.AddInput();
  auto b = graph.AddInput();
  auto c = graph.AddAnd(a, b);
  EXPECT_GT(graph.NodeCount(), 2);
  EXPECT_FALSE(AigIsCompl(c));
}

TEST(Aig, NotIsComplement) {
  AigGraph graph;
  auto a = graph.AddInput();
  auto not_a = graph.AddNot(a);
  EXPECT_EQ(AigVar(not_a), AigVar(a));
  EXPECT_NE(AigIsCompl(not_a), AigIsCompl(a));
}

TEST(Aig, OrViaDeMorgan) {
  AigGraph graph;
  auto a = graph.AddInput();
  auto b = graph.AddInput();
  auto c = graph.AddOr(a, b);
  EXPECT_GT(AigVar(c), 0);
}

TEST(SynthLower, AlwaysCombSimpleAssign) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b, output reg y);\n"
                           "  always_comb begin\n"
                           "    y = a & b;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 2);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(SynthLower, AcceptCombinationalModule) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b, output y);\n"
                           "  assign y = a & b;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SynthLower, AssignAndGate) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b, output y);\n"
                           "  assign y = a & b;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_NE(aig->outputs[0], AigGraph::kConstFalse);
  EXPECT_NE(aig->outputs[0], AigGraph::kConstTrue);
  EXPECT_GT(aig->NodeCount(), 3);
}

TEST(SynthLower, AssignOrGate) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b, output y);\n"
                           "  assign y = a | b;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_NE(aig->outputs[0], AigGraph::kConstFalse);
}

TEST(SynthLower, AssignNotGate) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, output y);\n"
                           "  assign y = ~a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  auto input_lit = AigLit(aig->inputs[0], false);
  EXPECT_EQ(aig->outputs[0], input_lit ^ 1u);
}

TEST(SynthLower, AssignXorGate) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b, output y);\n"
                           "  assign y = a ^ b;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_NE(aig->outputs[0], AigGraph::kConstFalse);
}

TEST(SynthLower, RejectSystemCall) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  reg x;\n"
                           "  always_comb begin x = $random; end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SynthLower, PortInputsMappedToAigInputs) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, input b, output y);\n"
                           "  assign y = a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 2);
  EXPECT_EQ(aig->outputs.size(), 1);
}

}  // namespace
