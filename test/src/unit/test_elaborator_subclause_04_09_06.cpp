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

RtlirModule* TopModule(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  return design->top_modules[0];
}

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

constexpr std::string_view kUdpOneBitTerminal =
    "user-defined primitive output terminal must be a 1-bit net";

::testing::AssertionResult ReportsTerminalWidth(const std::string& src,
                                                std::string_view message,
                                                uint32_t line) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(f.diag.Diagnostics(), message, line, "4.9.6");
}

::testing::AssertionResult ElaboratesCleanly(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  if (!f.has_errors) return ::testing::AssertionSuccess();
  return ::testing::AssertionFailure() << "an error was reported for:\n" << src;
}

std::string GateModule(const std::string& gate) {
  return "module top;\n"
         "  wire [3:0] wide;\n"
         "  wire s, t, en;\n"
         "  " +
         gate +
         "\n"
         "endmodule\n";
}

struct DrivenTerminalCase {
  std::string wide;
  std::string scalar;
};

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

TEST(PortConnectionElab, EveryGateTypeReportsAWideDrivenTerminal) {
  for (const DrivenTerminalCase& c : DrivenTerminalCases()) {
    EXPECT_TRUE(ReportsTerminalWidth(GateModule(c.wide), kOneBitTerminal, 4))
        << c.wide;
    EXPECT_TRUE(ElaboratesCleanly(GateModule(c.scalar))) << c.scalar;
  }
}

constexpr const char* kPassPrimitive =
    "primitive pass(output q, input a);\n"
    "  table\n"
    "    0 : 0;\n"
    "    1 : 1;\n"
    "  endtable\n"
    "endprimitive\n";

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

struct GenerateBlockForm {
  const char* open;
  const char* close;
};

constexpr GenerateBlockForm kGenerateBlocks[] = {
    {"  if (1) begin : g\n", "  end\n"},
    {"  case (1) 1: begin : g\n", "  end endcase\n"},
    {"  for (genvar i = 0; i < 2; i++) begin : g\n", "  end\n"}};

std::string InGenerateBlock(const GenerateBlockForm& block,
                            const std::string& module_decls,
                            const std::string& block_decl,
                            const std::string& inst) {
  return "module top;\n  " + module_decls + "\n" + block.open + "    " +
         block_decl + "\n    " + inst + "\n" + block.close + "endmodule\n";
}

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
