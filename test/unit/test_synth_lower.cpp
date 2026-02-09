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

// --- Test fixture ---

struct SynthFixture {
  SourceManager src_mgr;
  DiagEngine diag{src_mgr};
  Arena arena;
};

static const RtlirModule* ElaborateSrc(SynthFixture& f,
                                       const std::string& src) {
  auto fid = f.src_mgr.AddFile("<test>", src);
  Lexer lexer(f.src_mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  if (!cu || cu->modules.empty()) return nullptr;
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  if (!design || design->top_modules.empty()) return nullptr;
  return design->top_modules[0];
}

// =============================================================================
// Synthesizability checker
// =============================================================================

TEST(SynthLower, RejectInitialBlock) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f, "module m; initial begin end endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SynthLower, RejectDelay) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  reg x;\n"
                           "  always begin #10 x = 1; end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
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

// =============================================================================
// Port I/O mapping
// =============================================================================

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

TEST(SynthLower, MultiBitPortMapping) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input logic [3:0] a, output logic [3:0] y);\n"
                   "  assign y = a;\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 4);
  EXPECT_EQ(aig->outputs.size(), 4);
}

// =============================================================================
// Continuous assign lowering
// =============================================================================

TEST(SynthLower, AssignDirectWire) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, output y);\n"
                           "  assign y = a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 1);
  EXPECT_EQ(aig->outputs.size(), 1);
  EXPECT_EQ(aig->outputs[0], AigLit(aig->inputs[0], false));
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

TEST(SynthLower, AssignTernaryMux) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input sel, input a, input b, output y);\n"
                           "  assign y = sel ? a : b;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 3);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(SynthLower, AssignConstant) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output y);\n"
                           "  assign y = 1'b1;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
}

TEST(SynthLower, AssignConstantZero) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output y);\n"
                           "  assign y = 1'b0;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstFalse);
}

// =============================================================================
// Multi-bit assignment expansion
// =============================================================================

TEST(SynthLower, MultiBitAndGate) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input logic [1:0] a, input logic [1:0] b,\n"
                   "         output logic [1:0] y);\n"
                   "  assign y = a & b;\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 4);
  EXPECT_EQ(aig->outputs.size(), 2);
}

// =============================================================================
// always_comb lowering
// =============================================================================

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

TEST(SynthLower, AlwaysCombIfElse) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input sel, input a, input b, output reg y);\n"
                   "  always_comb begin\n"
                   "    if (sel) y = a;\n"
                   "    else y = b;\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 3);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(SynthLower, AlwaysCombCaseStmt) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input logic [1:0] sel, output logic [1:0] y);\n"
                   "  always_comb begin\n"
                   "    case (sel)\n"
                   "      2'b00: y = 2'b01;\n"
                   "      2'b01: y = 2'b10;\n"
                   "      default: y = 2'b00;\n"
                   "    endcase\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 2);
  EXPECT_EQ(aig->outputs.size(), 2);
}

// =============================================================================
// always_ff lowering
// =============================================================================

TEST(SynthLower, AlwaysFFRegistersLatch) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input d, output reg q);\n"
                           "  always_ff @(posedge clk) begin\n"
                           "    q <= d;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 1);
  EXPECT_FALSE(aig->latches.empty());
}

// =============================================================================
// always_latch lowering
// =============================================================================

TEST(SynthLower, AlwaysLatchCreatesLatch) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input en, input d, output reg q);\n"
                           "  always_latch begin\n"
                           "    if (en) q = d;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 1);
  EXPECT_FALSE(aig->latches.empty());
}
