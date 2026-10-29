#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The text every case below looks for. §4.9.6 is the only rule the elaborator
// enforces on the width of a primitive terminal, so finding this report is
// what distinguishes the rule from the other reasons a gate instantiation can
// be rejected -- an unresolved bound, a uwire terminal (§6.6.2), a
// user-defined net type mismatch (§28.8).
constexpr std::string_view kOneBitTerminal =
    "primitive output or inout terminal must be a 1-bit net";

TEST(PortConnectionElab, PrimitiveOutputMustBeOneBitNet) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] out;\n"
      "  logic in_sig;\n"
      "  buf b(out, in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOneBitTerminal, 4, "4.9.6"));
}

TEST(PortConnectionElab, PrimitiveOneBitOutputElaboratesCleanly) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire out;\n"
      "  logic in_sig;\n"
      "  buf b(out, in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PortConnectionElab, BidirectionalSwitchInoutMustBeOneBitNets) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [3:0] a, b;\n"
      "  tran t(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOneBitTerminal, 3, "4.9.6"));
}

// Positive boundary of the same rule for the inout half: a bidirectional
// switch whose terminals are 1-bit nets satisfies the direct-1-bit-net
// requirement and elaborates without error.
TEST(PortConnectionElab, BidirectionalSwitchOneBitInoutElaboratesCleanly) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire a, b;\n"
      "  tran t(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §4.9.6 admits a 1-bit *structural net expression* (see 23.3.3), not only a
// scalar net, as a primitive output/inout terminal. A single-bit select of a
// vector net is one bit wide and satisfies the rule.
TEST(PortConnectionElab, PrimitiveOutputOneBitSelectElaboratesCleanly) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b(bus[0], in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// Negative form of the same rule for a structural net expression: a ranged
// part-select wider than one bit driving a primitive output terminal violates
// the 1-bit requirement.
TEST(PortConnectionElab, PrimitiveOutputMultiBitPartSelectRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b(bus[3:1], in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOneBitTerminal, 4, "4.9.6"));
}

// The part-select bounds are a constant expression (§11.2.1); a localparam is
// one of its constant forms. The 1-bit rule must measure the select width after
// resolving the localparam bounds, so a 3-bit localparam-bounded part-select is
// rejected just like a literal-bounded one. Naming the report matters most
// here: a run that never folded HI and LO would leave the width unmeasured and
// reject the source for some other reason, which a bare error count cannot
// tell apart from the rule firing.
TEST(PortConnectionElab, PrimitiveOutputPartSelectWidthFromLocalparam) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  localparam int HI = 3;\n"
      "  localparam int LO = 1;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b(bus[HI:LO], in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOneBitTerminal, 6, "4.9.6"));
}

// An indexed part-select `[base +: width]` is another structural net expression
// form (§23.3.3). With a width of one it names a single bit and satisfies the
// primitive-terminal 1-bit rule.
TEST(PortConnectionElab,
     PrimitiveOutputIndexedPartSelectOneBitElaboratesCleanly) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b(bus[2 +: 1], in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// Negative form: an indexed part-select spanning more than one bit driving a
// primitive output terminal violates the 1-bit rule.
TEST(PortConnectionElab, PrimitiveOutputIndexedPartSelectMultiBitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b(bus[2 +: 3], in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOneBitTerminal, 4, "4.9.6"));
}

// A concatenation of net selects is a structural net expression (§23.3.3). A
// concatenation whose parts total one bit satisfies the 1-bit rule.
TEST(PortConnectionElab, PrimitiveOutputConcatOneBitElaboratesCleanly) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b({bus[0]}, in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// Negative form: a concatenation whose parts total more than one bit driving a
// primitive output terminal violates the 1-bit rule.
TEST(PortConnectionElab, PrimitiveOutputConcatMultiBitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b({bus[1:0]}, in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOneBitTerminal, 4, "4.9.6"));
}

// The 1-bit rule covers the *inout* terminal position as well as output. A
// bidirectional switch terminal driven by a multi-bit structural net expression
// (a ranged part-select) is rejected just like a multi-bit output terminal.
TEST(PortConnectionElab, PrimitiveInoutMultiBitPartSelectRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  wire other;\n"
      "  tran t(bus[3:1], other);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOneBitTerminal, 4, "4.9.6"));
}

// A module parameter is another constant form (§11.2.1) admissible as a
// part-select bound, taking the overridable-parameter code path rather than the
// localparam one. A 3-bit parameter-bounded part-select is still rejected.
TEST(PortConnectionElab, PrimitiveOutputPartSelectWidthFromParameter) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter int HI = 3) ();\n"
      "  wire [7:0] bus;\n"
      "  logic in_sig;\n"
      "  buf b(bus[HI:1], in_sig);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kOneBitTerminal, 4, "4.9.6"));
}

// The rest of this file covers the same rule for a user-defined primitive
// instance rather than a gate instance. §4.9.6 states it for both in one
// sentence -- primitive terminals, UDP terminals among them, are not module
// ports, and a primitive's output and inout terminals connect straight to 1-bit
// nets or 1-bit structural net expressions -- and §29.8 adds of a UDP
// instantiation that it connects its terminals by §28.3.6's rules.
//
// The report a UDP instance provokes names its output terminal alone, because
// §29.3.1 gives a UDP many inputs, one output and no inout port at all. That is
// different wording from the gate report kOneBitTerminal above matches, so the
// two cases below spell out their own, width included: a run that measured an
// input terminal or the vector's bounds instead of the output terminal's width
// reports a different number, and matching the number is what tells those
// apart.
//
// These are the cases #3200 was filed on. ValidatePrimitiveOutputTerminalWidths
// (src/elaborator/elaborator_gates.cpp) returned at once on any item that was
// not a ModuleItemKind::kGateInst, and the kUdpInst arm of
// Elaborator::ElaborateDeclItem (src/elaborator/elaborator_items.cpp) did not
// call it, so a primitive instance with a four-bit output terminal elaborated
// in silence -- while UdpEvalState (src/simulator/udp_eval.h) answers one of
// '0', '1' and 'x', so one bit is all the instance ever drives.

// The top module of a design ElaborateSrc built, or nullptr when the elaborator
// rooted none. Each case below names its own top, so a design that reached the
// assertions holds exactly that one.
RtlirModule* TopModule(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  return design->top_modules[0];
}

// §4.9.6: the output terminal of the primitive instance below is connected to a
// four-bit net, which is neither a 1-bit net nor a 1-bit structural net
// expression, so the source shall be rejected. The width is 4 while the net is
// declared `[3:0]`, so a run reporting a bound rather than the width says 3 and
// fails here.
TEST(PortConnectionElab, PrimitiveInstanceWithAWideOutputTerminalIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "primitive p_wide4(output q_out, input i_a, input i_b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module wide4_top;\n"
      "  wire [3:0] q_bus;\n"
      "  wire i_a_s, i_b_s;\n"
      "  p_wide4 u_wide4(q_bus, i_a_s, i_b_s);\n"
      "endmodule\n",
      f, "wide4_top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "user-defined primitive output terminal must be a "
                            "1-bit net or structural net expression (got "
                            "width 4)",
                            12, "4.9.6"));
}

// §4.9.6 admits a 1-bit *structural net expression* (see 23.3.3) as a primitive
// output terminal, and a ranged part-select spanning more than one bit is not
// one, so the source shall be rejected. The select is `[4:2]` of a `[7:0]`
// net: the width 3 is neither bound, and it is not the declared width 8, so a
// run that read a bound or the whole net instead of the span reports a
// different number and fails here.
TEST(PortConnectionElab, PrimitiveInstanceWithAWideOutputSelectIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "primitive p_sel3(output q_out, input i_a, input i_b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : 1;\n"
      "    1 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module sel3_top;\n"
      "  wire [7:0] q_bus;\n"
      "  wire i_a_s, i_b_s;\n"
      "  p_sel3 u_sel3(q_bus[4:2], i_a_s, i_b_s);\n"
      "endmodule\n",
      f, "sel3_top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "user-defined primitive output terminal must be a "
                            "1-bit net or structural net expression (got "
                            "width 3)",
                            12, "4.9.6"));
}

// The conforming case of the same rule: a scalar net is the 1-bit net §4.9.6
// requires, so the design shall elaborate and the instance shall reach
// RtlirModule::udp_insts (src/elaborator/rtlir.h) driving that net. Reading the
// recorded instance back is what separates "accepted" from "dropped without a
// report", and it is what fails if the widened check starts rejecting a source
// the standard allows.
TEST(PortConnectionElab, PrimitiveInstanceWithAScalarOutputTerminalIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive p_scal1(output q_out, input i_a, input i_b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module scal1_top;\n"
      "  wire q_scalar;\n"
      "  wire i_a_s, i_b_s;\n"
      "  p_scal1 u_scal1(q_scalar, i_a_s, i_b_s);\n"
      "endmodule\n",
      f, "scal1_top");
  auto* mod = TopModule(design);
  ASSERT_NE(mod, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(mod->udp_insts.size(), 1U);
  ASSERT_NE(mod->udp_insts[0].output, nullptr);
  EXPECT_EQ(mod->udp_insts[0].output->text, "q_scalar");
}

// An instance array is the one place a terminal wider than one bit satisfies
// §4.9.6, so the four-bit terminal below shall draw no report. §28.3.6 rules
// that where the widths differ, each instance takes a part-select of the port
// expression as wide as its own port, and §29.8 has a UDP instance connect its
// terminals by §28.3.6's rules, so each of the four elements connects to one
// bit and the whole terminal is not the width the rule measures.
// ValidatePrimitiveOutputTerminalWidths returns early on an instance array for
// that reason, and this case says the early return still holds now that its
// kind guard admits a primitive instance: a check that measured the terminal
// anyway would reject this source with the §4.9.6 report the two cases above
// look for.
//
// The instance range is `[7:4]` and the terminal is declared `[3:0]` so that no
// array index is also a bit position of the terminal, and the four recorded
// instances are asserted alongside the absence of errors so that an expansion
// that dropped the array cannot pass.
TEST(PortConnectionElab,
     PrimitiveInstanceArrayWithAWideOutputTerminalIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive p_arr4(output q_out, input i_a, input i_b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module arr4_top;\n"
      "  wire [3:0] q_bus;\n"
      "  wire i_a_s, i_b_s;\n"
      "  p_arr4 u_arr4 [7:4] (q_bus, i_a_s, i_b_s);\n"
      "endmodule\n",
      f, "arr4_top");
  auto* mod = TopModule(design);
  ASSERT_NE(mod, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(mod->udp_insts.size(), 4U);
}

// The report a user-defined primitive instance's output terminal draws.
constexpr std::string_view kUdpOneBitTerminal =
    "user-defined primitive output terminal must be a 1-bit net";

// Whether elaborating `src` reports `message` under §4.9.6 at `line`.
::testing::AssertionResult ReportsTerminalWidth(const std::string& src,
                                                std::string_view message,
                                                uint32_t line) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(f.diag.Diagnostics(), message, line, "4.9.6");
}

// Whether `src` elaborates without an error.
::testing::AssertionResult ElaboratesCleanly(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  if (!f.has_errors) return ::testing::AssertionSuccess();
  return ::testing::AssertionFailure() << "an error was reported for:\n" << src;
}

// A module whose nets are the four-bit `wide` and the scalars `s`, `t` and
// `en`, with the gate instance `gate` on line 4.
std::string GateModule(const std::string& gate) {
  return "module top;\n"
         "  wire [3:0] wide;\n"
         "  wire s, t, en;\n"
         "  " +
         gate +
         "\n"
         "endmodule\n";
}

// One gate instance with a four-bit net on a driven terminal, and the same
// instance with a scalar net there.
struct DrivenTerminalCase {
  std::string wide;
  std::string scalar;
};

// Each gate type of Syntax 28-1 with every terminal §28 makes driven: the
// outputs of an n-input, enable, MOS, CMOS and pull gate, each output of an
// n-output gate, the later one included, and either inout terminal of a pass
// switch and of an enabled pass switch.
std::vector<DrivenTerminalCase> DrivenTerminalCases() {
  std::vector<DrivenTerminalCase> cases;
  for (const char* gate : {"buf", "not"}) {
    cases.push_back({std::string(gate) + " g(wide, s, en);",
                     std::string(gate) + " g(t, s, en);"});
    cases.push_back({std::string(gate) + " g(s, wide, en);",
                     std::string(gate) + " g(s, t, en);"});
  }
  for (const char* gate :
       {"and", "or", "nand", "nor", "xor", "xnor", "bufif0", "bufif1", "notif0",
        "notif1", "nmos", "pmos", "rnmos", "rpmos", "tranif0", "tranif1",
        "rtranif0", "rtranif1"}) {
    cases.push_back({std::string(gate) + " g(wide, s, en);",
                     std::string(gate) + " g(t, s, en);"});
  }
  for (const char* gate : {"cmos", "rcmos"}) {
    cases.push_back({std::string(gate) + " g(wide, s, en, t);",
                     std::string(gate) + " g(s, t, en, en);"});
  }
  for (const char* gate : {"pullup", "pulldown"}) {
    cases.push_back(
        {std::string(gate) + " g(wide);", std::string(gate) + " g(t);"});
  }
  for (const char* gate :
       {"tran", "rtran", "tranif0", "tranif1", "rtranif0", "rtranif1"}) {
    std::string controls =
        std::string(gate).find("if") == std::string::npos ? ");" : ", en);";
    cases.push_back({std::string(gate) + " g(s, wide" + controls,
                     std::string(gate) + " g(s, t" + controls});
  }
  return cases;
}

// §4.9.6 holds every output and inout terminal of every primitive to one bit,
// so a four-bit net on any driven terminal of any gate type is reported, and
// the same instance with a scalar net there is accepted.
TEST(PortConnectionElab, EveryGateTypeReportsAWideDrivenTerminal) {
  for (const DrivenTerminalCase& c : DrivenTerminalCases()) {
    EXPECT_TRUE(ReportsTerminalWidth(GateModule(c.wide), kOneBitTerminal, 4))
        << c.wide;
    EXPECT_TRUE(ElaboratesCleanly(GateModule(c.scalar))) << c.scalar;
  }
}

// The primitive that the cases below instantiate, on lines 1 to 6.
constexpr const char* kPassPrimitive =
    "primitive pass(output q, input a);\n"
    "  table\n"
    "    0 : 0;\n"
    "    1 : 1;\n"
    "  endtable\n"
    "endprimitive\n";

// §10.3.2 lets one primitive output drive a variable, and §4.9.6 holds the
// terminal to one bit whatever it connects, so a four-bit variable on a gate's
// or a user-defined primitive's output is reported beside a 1-bit variable
// accepted.
TEST(PortConnectionElab, AVectorVariableOnAPrimitiveOutputIsReported) {
  const std::string kDecls =
      "module top;\n"
      "  logic [3:0] v;\n"
      "  logic b;\n"
      "  wire s;\n";
  EXPECT_TRUE(ReportsTerminalWidth(kDecls + "  buf g(v, s);\nendmodule\n",
                                   kOneBitTerminal, 5));
  EXPECT_TRUE(ElaboratesCleanly(kDecls + "  buf g(b, s);\nendmodule\n"));
  EXPECT_TRUE(ReportsTerminalWidth(
      kPassPrimitive + kDecls + "  pass u(v, s);\nendmodule\n",
      kUdpOneBitTerminal, 11));
  EXPECT_TRUE(ElaboratesCleanly(kPassPrimitive + kDecls +
                                "  pass u(b, s);\nendmodule\n"));
}

// The three generate block forms, each opening and closing on one line, the
// block named g.
struct GenerateBlockForm {
  const char* open;
  const char* close;
};

constexpr GenerateBlockForm kGenerateBlocks[] = {
    {"  if (1) begin : g\n", "  end\n"},
    {"  case (1) 1: begin : g\n", "  end endcase\n"},
    {"  for (genvar i = 0; i < 2; i++) begin : g\n", "  end\n"}};

// A module declaring `module_decls` on line 2 and, in a generate block of form
// `block`, `block_decl` on line 4 and the primitive instance `inst` on line 5.
std::string InGenerateBlock(const GenerateBlockForm& block,
                            const std::string& module_decls,
                            const std::string& block_decl,
                            const std::string& inst) {
  return "module top;\n  " + module_decls + "\n" + block.open + "    " +
         block_decl + "\n    " + inst + "\n" + block.close + "endmodule\n";
}

// §27.4 makes a generate block a scope whose declarations a primitive in it
// connects to, and §4.9.6 measures the net the terminal names: a four-bit net
// the block declares is reported, in an if, a case and a loop generate block,
// beside a scalar net the block declares accepted.
TEST(PortConnectionElab, AGenerateBlocksOwnNetIsMeasuredAtAPrimitiveOutput) {
  for (const GenerateBlockForm& block : kGenerateBlocks) {
    EXPECT_TRUE(ReportsTerminalWidth(
        InGenerateBlock(block, "wire s;", "wire [3:0] w;", "buf b(w, s);"),
        kOneBitTerminal, 5))
        << block.open;
    EXPECT_TRUE(ElaboratesCleanly(
        InGenerateBlock(block, "wire s;", "wire w;", "buf b(w, s);")))
        << block.open;
  }
}

// §23.9: a name a generate block declares hides the module's declaration of
// it inside the block, so the terminal is as wide as the block's net: a
// four-bit block net over a scalar module net is reported, and a scalar block
// net over a four-bit module net is accepted.
TEST(PortConnectionElab,
     AGenerateBlocksNetShadowsTheModulesAtAPrimitiveOutput) {
  for (const GenerateBlockForm& block : kGenerateBlocks) {
    EXPECT_TRUE(ReportsTerminalWidth(
        InGenerateBlock(block, "wire s, w;", "wire [3:0] w;", "buf b(w, s);"),
        kOneBitTerminal, 5))
        << block.open;
    EXPECT_TRUE(ElaboratesCleanly(InGenerateBlock(
        block, "wire s; wire [3:0] w;", "wire w;", "buf b(w, s);")))
        << block.open;
  }
}

// The same for a user-defined primitive's output terminal in a generate block,
// the primitive declared on the six lines before the module.
TEST(PortConnectionElab,
     APrimitiveInstanceInAGenerateBlockMeasuresTheBlocksNet) {
  for (const GenerateBlockForm& block : kGenerateBlocks) {
    EXPECT_TRUE(ReportsTerminalWidth(
        kPassPrimitive + InGenerateBlock(block, "wire s, w;", "wire [3:0] w;",
                                         "pass u(w, s);"),
        kUdpOneBitTerminal, 11))
        << block.open;
    EXPECT_TRUE(ElaboratesCleanly(
        kPassPrimitive + InGenerateBlock(block, "wire s; wire [3:0] w;",
                                         "wire w;", "pass u(w, s);")))
        << block.open;
  }
}

// §27.4 gives each instance of a loop generate block its genvar as a constant,
// so a part-select bounded by it has a width §4.9.6 measures: two bits is
// reported, one bit accepted.
TEST(PortConnectionElab, AGenvarBoundedPartSelectIsMeasuredAtAPrimitiveOutput) {
  const std::string kOpen =
      "module top;\n"
      "  wire s;\n"
      "  wire [7:0] w;\n"
      "  for (genvar i = 0; i < 4; i++) begin : g\n";
  const std::string kClose = "  end\nendmodule\n";
  EXPECT_TRUE(ReportsTerminalWidth(
      kOpen + "    buf b(w[2*i+1:2*i], s);\n" + kClose, kOneBitTerminal, 5));
  EXPECT_TRUE(ElaboratesCleanly(kOpen + "    buf b(w[i:i], s);\n" + kClose));
}

}  // namespace
