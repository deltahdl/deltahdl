// §10.3: Continuous assignments

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "synthesis/aig.h"
#include "synthesis/synth_lower.h"

using namespace delta;

struct SynthFixture {
  SourceManager src_mgr;
  DiagEngine diag{src_mgr};
  Arena arena;
};

static const RtlirModule *ElaborateSrc(SynthFixture &f,
                                       const std::string &src) {
  auto fid = f.src_mgr.AddFile("<test>", src);
  Lexer lexer(f.src_mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  if (!cu || cu->modules.empty())
    return nullptr;
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  if (!design || design->top_modules.empty())
    return nullptr;
  return design->top_modules[0];
}

namespace {

TEST(SynthLower, AcceptCombinationalModule) {
  SynthFixture f;
  auto *mod = ElaborateSrc(f, "module m(input a, input b, output y);\n"
                              "  assign y = a & b;\n"
                              "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SynthLower, AssignDirectWire) {
  SynthFixture f;
  auto *mod = ElaborateSrc(f, "module m(input a, output y);\n"
                              "  assign y = a;\n"
                              "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 1);
  EXPECT_EQ(aig->outputs.size(), 1);
  EXPECT_EQ(aig->outputs[0], AigLit(aig->inputs[0], false));
}

TEST(SynthLower, AssignAndGate) {
  SynthFixture f;
  auto *mod = ElaborateSrc(f, "module m(input a, input b, output y);\n"
                              "  assign y = a & b;\n"
                              "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_NE(aig->outputs[0], AigGraph::kConstFalse);
  EXPECT_NE(aig->outputs[0], AigGraph::kConstTrue);
  EXPECT_GT(aig->NodeCount(), 3);
}

TEST(SynthLower, AssignOrGate) {
  SynthFixture f;
  auto *mod = ElaborateSrc(f, "module m(input a, input b, output y);\n"
                              "  assign y = a | b;\n"
                              "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_NE(aig->outputs[0], AigGraph::kConstFalse);
}

TEST(SynthLower, AssignNotGate) {
  SynthFixture f;
  auto *mod = ElaborateSrc(f, "module m(input a, output y);\n"
                              "  assign y = ~a;\n"
                              "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  auto input_lit = AigLit(aig->inputs[0], false);
  EXPECT_EQ(aig->outputs[0], input_lit ^ 1u);
}

TEST(SynthLower, AssignXorGate) {
  SynthFixture f;
  auto *mod = ElaborateSrc(f, "module m(input a, input b, output y);\n"
                              "  assign y = a ^ b;\n"
                              "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_NE(aig->outputs[0], AigGraph::kConstFalse);
}

TEST(SynthLower, AssignTernaryMux) {
  SynthFixture f;
  auto *mod =
      ElaborateSrc(f, "module m(input sel, input a, input b, output y);\n"
                      "  assign y = sel ? a : b;\n"
                      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 3);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(SynthLower, AssignConstant) {
  SynthFixture f;
  auto *mod = ElaborateSrc(f, "module m(output y);\n"
                              "  assign y = 1'b1;\n"
                              "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
}

TEST(SynthLower, AssignConstantZero) {
  SynthFixture f;
  auto *mod = ElaborateSrc(f, "module m(output y);\n"
                              "  assign y = 1'b0;\n"
                              "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstFalse);
}

TEST(SynthLower, MultiBitAndGate) {
  SynthFixture f;
  auto *mod =
      ElaborateSrc(f, "module m(input logic [1:0] a, input logic [1:0] b,\n"
                      "         output logic [1:0] y);\n"
                      "  assign y = a & b;\n"
                      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 4);
  EXPECT_EQ(aig->outputs.size(), 2);
}

} // namespace
