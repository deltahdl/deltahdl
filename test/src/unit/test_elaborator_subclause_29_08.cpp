#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <set>
#include <string>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_primitives.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

RtlirModule* TopModule(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  return design->top_modules[0];
}

TEST(UdpInstanceElaboration, CombinationalPrimitiveDrivesItsOutputTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive p_and2(output q_out, input sel_a, input sel_b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module drv_top;\n"
      "  wire q_out, sel_a, sel_b;\n"
      "  p_and2 u_drv(q_out, sel_a, sel_b);\n"
      "endmodule\n",
      f, "drv_top");
  auto* mod = TopModule(design);
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->udp_insts.size(), 1U);
  ASSERT_NE(mod->udp_insts[0].output, nullptr);
  EXPECT_EQ(mod->udp_insts[0].output->text, "q_out");
}

TEST(UdpInstanceElaboration, TerminalOrderFollowsThePrimitiveDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive p_ord3(output m_out, input i_first, input i_second,\n"
      "                 input i_third);\n"
      "  table\n"
      "    0 0 0 : 0;\n"
      "    1 0 0 : 1;\n"
      "    0 1 0 : 1;\n"
      "    0 0 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module ord_top;\n"
      "  wire m_out, i_first, i_second, i_third;\n"
      "  p_ord3 u_ord(m_out, i_first, i_second, i_third);\n"
      "endmodule\n",
      f, "ord_top");
  auto* mod = TopModule(design);
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->udp_insts.size(), 1U);
  const auto& inst = mod->udp_insts[0];
  ASSERT_NE(inst.output, nullptr);
  ASSERT_EQ(inst.inputs.size(), 3U);
  EXPECT_EQ(inst.output->text, "m_out");
  EXPECT_EQ(inst.inputs[0]->text, "i_first");
  EXPECT_EQ(inst.inputs[1]->text, "i_second");
  EXPECT_EQ(inst.inputs[2]->text, "i_third");
}

TEST(UdpInstanceElaboration, InstanceCarriesTheDeclarationItNamed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive p_other1(output o_alt, input i_alt);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "primitive p_named2(output o_named, input i_left, input i_right);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : 1;\n"
      "    1 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module decl_top;\n"
      "  wire o_named, i_left, i_right;\n"
      "  p_named2 u_decl(o_named, i_left, i_right);\n"
      "endmodule\n",
      f, "decl_top");
  auto* mod = TopModule(design);
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->udp_insts.size(), 1U);
  ASSERT_NE(mod->udp_insts[0].decl, nullptr);
  EXPECT_EQ(mod->udp_insts[0].decl->name, "p_named2");
  EXPECT_EQ(mod->udp_insts[0].decl->output_name, "o_named");
}

TEST(UdpInstanceElaboration, DelayAndDriveStrengthReachTheInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive p_buf1(output d_out, input d_in);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module delay_top;\n"
      "  wire d_out, d_in;\n"
      "  p_buf1 (strong1, weak0) #5 u_delay(d_out, d_in);\n"
      "endmodule\n",
      f, "delay_top");
  auto* mod = TopModule(design);
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->udp_insts.size(), 1U);
  const auto& inst = mod->udp_insts[0];
  ASSERT_NE(inst.delay, nullptr);
  EXPECT_EQ(inst.delay->int_val, 5U);
  EXPECT_EQ(inst.drive_strength1, 4);
  EXPECT_EQ(inst.drive_strength0, 2);
}

TEST(UdpInstanceElaboration, UnnamedInstanceElaboratesWithAnEmptyName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive p_inv1(output n_out, input n_in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module anon_top;\n"
      "  wire n_out, n_in;\n"
      "  p_inv1 (n_out, n_in);\n"
      "endmodule\n",
      f, "anon_top");
  auto* mod = TopModule(design);
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->udp_insts.size(), 1U);
  const auto& inst = mod->udp_insts[0];
  ASSERT_NE(inst.output, nullptr);
  ASSERT_EQ(inst.inputs.size(), 1U);
  EXPECT_EQ(inst.name, "");
  EXPECT_EQ(inst.output->text, "n_out");
  EXPECT_EQ(inst.inputs[0]->text, "n_in");
}

TEST(UdpInstanceElaboration, GateInstanceInTheSameModuleStaysInAssigns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive p_xor2(output x_out, input x_a, input x_b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : 1;\n"
      "    1 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module mixed_top;\n"
      "  wire x_out, x_a, x_b, g_out;\n"
      "  p_xor2 u_prim(x_out, x_a, x_b);\n"
      "  and u_gate(g_out, x_a, x_b);\n"
      "endmodule\n",
      f, "mixed_top");
  auto* mod = TopModule(design);
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->udp_insts.size(), 1U);
  ASSERT_EQ(mod->assigns.size(), 1U);
  ASSERT_NE(mod->udp_insts[0].output, nullptr);
  ASSERT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_EQ(mod->udp_insts[0].output->text, "x_out");
  EXPECT_EQ(mod->assigns[0].lhs->text, "g_out");
}

TEST(UdpInstanceElaboration, InstanceArrayExpandsToOneInstancePerElement) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive p_arr1(output r_out, input r_in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module arr_top;\n"
      "  wire [3:0] r_out_v, r_in_v;\n"
      "  p_arr1 u_arr [7:4] (r_out_v, r_in_v);\n"
      "endmodule\n",
      f, "arr_top");
  auto* mod = TopModule(design);
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->udp_insts.size(), 4U);
  std::set<uint64_t> output_bits;
  for (const auto& inst : mod->udp_insts) {
    ASSERT_NE(inst.output, nullptr);
    ASSERT_EQ(inst.output->kind, ExprKind::kSelect);
    ASSERT_NE(inst.output->base, nullptr);
    ASSERT_NE(inst.output->index, nullptr);
    EXPECT_EQ(inst.output->base->text, "r_out_v");
    output_bits.insert(inst.output->index->int_val);
  }
  EXPECT_EQ(output_bits, (std::set<uint64_t>{0, 1, 2, 3}));
}

TEST(UdpInstanceElaboration, InstanceArrayTerminalOfAWrongWidthIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "primitive p_wide1(output w_out, input w_in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module wide_top;\n"
      "  wire [2:0] w_out_v;\n"
      "  wire w_in_s;\n"
      "  p_wide1 u_wide [7:4] (w_out_v, w_in_s);\n"
      "endmodule\n",
      f, "wide_top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "gate or primitive array terminal width does not match", 10, "28.3.6"));
}

TEST(UdpInstanceElaboration, GenerateLoopStampsEachInstanceWithItsIndex) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive p_row1(output y_out, input y_in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module row_top;\n"
      "  wire [7:4] y_out_v, y_in_v;\n"
      "  genvar row;\n"
      "  generate\n"
      "    for (row = 5; row < 7; row = row + 1) begin : row_blk\n"
      "      p_row1 u_row(y_out_v[row], y_in_v[row]);\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "row_top");
  auto* mod = TopModule(design);
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->udp_insts.size(), 2U);
  std::set<int64_t> index_values;
  for (const auto& inst : mod->udp_insts) {
    ASSERT_EQ(inst.gen_block_consts.size(), 1U);
    EXPECT_EQ(inst.gen_block_consts[0].first, "row");
    index_values.insert(inst.gen_block_consts[0].second);
  }
  EXPECT_EQ(index_values, (std::set<int64_t>{5, 6}));
}

TEST(UdpInstanceElaboration, GenerateBlockPrefixNamesTheInstanceDeclarations) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive p_col1(output c_out, input c_in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module col_top;\n"
      "  wire c_in_s;\n"
      "  genvar col;\n"
      "  generate\n"
      "    for (col = 9; col < 10; col = col + 1) begin : col_blk\n"
      "      wire c_local;\n"
      "      p_col1 u_col(c_local, c_in_s);\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f, "col_top");
  auto* mod = TopModule(design);
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->udp_insts.size(), 1U);
  const RtlirNet* block_net = nullptr;
  for (const auto& net : mod->nets) {
    if (net.name.ends_with("c_local")) block_net = &net;
  }
  ASSERT_NE(block_net, nullptr);
  ASSERT_NE(block_net->name, "c_local");
  ASSERT_FALSE(mod->udp_insts[0].gen_block_prefixes.empty());
  EXPECT_EQ(
      std::string(mod->udp_insts[0].gen_block_prefixes.back()) + "c_local",
      std::string(block_net->name));
}

TEST(UdpInstanceElaboration, InstanceWithTooFewTerminalsIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "primitive p_two(output t_out, input t_a, input t_b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module few_top;\n"
      "  wire t_out, t_a;\n"
      "  p_two u_few(t_out, t_a);\n"
      "endmodule\n",
      f, "few_top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "primitive 'p_two' takes 3 terminal(s) but this instance connects 2", 9,
      "29.8"));
}

TEST(UdpInstanceElaboration, InstanceWithTooManyTerminalsIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "primitive p_two(output t_out, input t_a, input t_b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module many_top;\n"
      "  wire t_out, t_a, t_b, t_c;\n"
      "  p_two u_many(t_out, t_a, t_b, t_c);\n"
      "endmodule\n",
      f, "many_top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "primitive 'p_two' takes 3 terminal(s) but this instance connects 4", 9,
      "29.8"));
}

TEST(UdpInstanceElaboration, InstanceArrayTerminalCountIsReportedOnce) {
  ElabFixture f;
  ElaborateSrc(
      "primitive p_two(output t_out, input t_a, input t_b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module arr_few_top;\n"
      "  wire [3:0] t_out_v, t_a_v;\n"
      "  p_two u_arr_few [7:4] (t_out_v, t_a_v);\n"
      "endmodule\n",
      f, "arr_few_top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "primitive 'p_two' takes 3 terminal(s) but this instance connects 2", 9,
      "29.8"));
  const auto& diags = f.diag.Diagnostics();
  auto count_reports =
      std::count_if(diags.begin(), diags.end(), [](const Diagnostic& d) {
        return d.message.find("terminal(s) but this instance connects") !=
               std::string::npos;
      });
  EXPECT_EQ(count_reports, 1);
}

std::string ForwardUdpSrc(const std::string& inst) {
  return "module fwd_top;\n"
         "  wire f_out, f_a, f_b;\n"
         "  " +
         inst +
         "\n"
         "endmodule\n"
         "primitive p_fwd(output f_out, input f_a, input f_b);\n"
         "  table\n"
         "    0 0 : 0;\n"
         "    1 1 : 1;\n"
         "  endtable\n"
         "endprimitive\n";
}

const RtlirUdpInst* ForwardUdpInst(RtlirDesign* design) {
  auto* mod = TopModule(design);
  if (mod == nullptr || mod->udp_insts.size() != 1) return nullptr;
  return &mod->udp_insts[0];
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpTakesAParenthesisedDelay) {
  ElabFixture f;
  const auto* inst = ForwardUdpInst(ElaborateSrc(
      ForwardUdpSrc("p_fwd #(5) u(f_out, f_a, f_b);"), f, "fwd_top"));
  ASSERT_NE(inst, nullptr);
  ASSERT_NE(inst->delay, nullptr);
  EXPECT_EQ(inst->delay->int_val, 5U);
  EXPECT_EQ(inst->delay_fall, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpWithAnEmptyDelayIsReported) {
  ElabFixture f;
  ElaborateSrc(ForwardUdpSrc("p_fwd #() u(f_out, f_a, f_b);"), f, "fwd_top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a UDP instance's #( ) holds one or two delays, "
                            "not none",
                            3, "A.5.4"));
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpTakesRiseAndFallDelays) {
  ElabFixture f;
  const auto* inst = ForwardUdpInst(ElaborateSrc(
      ForwardUdpSrc("p_fwd #(5, 3) u(f_out, f_a, f_b);"), f, "fwd_top"));
  ASSERT_NE(inst, nullptr);
  ASSERT_NE(inst->delay, nullptr);
  ASSERT_NE(inst->delay_fall, nullptr);
  EXPECT_EQ(inst->delay->int_val, 5U);
  EXPECT_EQ(inst->delay_fall->int_val, 3U);
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpWithThreeDelaysIsReported) {
  ElabFixture f;
  ElaborateSrc(ForwardUdpSrc("p_fwd #(5, 3, 1) u(f_out, f_a, f_b);"), f,
               "fwd_top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "UDP instantiation shall have at most two delays",
                            3, "29.8"));
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpWithANamedAssignmentIsReported) {
  ElabFixture f;
  ElaborateSrc(ForwardUdpSrc("p_fwd #(.d(5)) u(f_out, f_a, f_b);"), f,
               "fwd_top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a UDP instance takes its delays in order, not a named assignment", 3,
      "29.8"));
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpWithNamedConnectionsIsReported) {
  ElabFixture f;
  ElaborateSrc(ForwardUdpSrc("p_fwd u(.f_b(f_b), .f_out(f_out), .f_a(f_a));"),
               f, "fwd_top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a UDP instance connects its terminals in order, not by name", 3,
      "29.8"));
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpWithAWildcardIsReported) {
  ElabFixture f;
  ElaborateSrc(ForwardUdpSrc("p_fwd u(.*);"), f, "fwd_top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a UDP instance connects its terminals in order, not by name", 3,
      "29.8"));
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpTakesADelayWithoutParentheses) {
  ElabFixture f;
  const auto* inst = ForwardUdpInst(ElaborateSrc(
      ForwardUdpSrc("p_fwd #5 u(f_out, f_a, f_b);"), f, "fwd_top"));
  ASSERT_NE(inst, nullptr);
  ASSERT_NE(inst->delay, nullptr);
  EXPECT_EQ(inst->delay->int_val, 5U);
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpTakesADriveStrength) {
  ElabFixture f;
  const auto* inst = ForwardUdpInst(
      ElaborateSrc(ForwardUdpSrc("p_fwd (strong0, weak1) u(f_out, f_a, f_b);"),
                   f, "fwd_top"));
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->drive_strength0, 4);
  EXPECT_EQ(inst->drive_strength1, 2);
}

TEST(UdpInstanceElaboration, UnnamedInstanceOfAForwardDeclaredUdp) {
  ElabFixture f;
  const auto* inst = ForwardUdpInst(
      ElaborateSrc(ForwardUdpSrc("p_fwd (f_out, f_a, f_b);"), f, "fwd_top"));
  ASSERT_NE(inst, nullptr);
  ASSERT_NE(inst->output, nullptr);
  EXPECT_EQ(inst->output->text, "f_out");
}

TEST(UdpInstanceElaboration, ModuleWrittenAsAPrimitiveInstanceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m_child(output o, input i);\n"
      "endmodule\n"
      "module fwd_top;\n"
      "  wire f_out, f_a;\n"
      "  m_child #5 u(f_out, f_a);\n"
      "endmodule\n",
      f, "fwd_top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'m_child' is instantiated as a user-defined "
                            "primitive, but no primitive has that name",
                            5, "29.8"));
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpArrayWithASecondRange) {
  ElabFixture f;
  ElaborateSrc(ForwardUdpSrc("p_fwd u[1:0][1:0](f_out, f_a, f_b);"), f,
               "fwd_top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an array of instances takes a single range after "
                            "its instance identifier, not a second one",
                            3, "28.3.5"));
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpArrayWithASizeAlone) {
  ElabFixture f;
  ElaborateSrc(ForwardUdpSrc("p_fwd u[2](f_out, f_a, f_b);"), f, "fwd_top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an array of instances is declared by a range of "
                            "two constant expressions",
                            3, "28.3.5"));
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpArrayWithOneRange) {
  ElabFixture f;
  ElaborateSrc(ForwardUdpSrc("p_fwd u[1:0](f_out, f_a, f_b);"), f, "fwd_top");
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "an array of instances", 3,
                             "28.3.5"));
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpWithAnEmptyOutputTerminal) {
  ElabFixture f;
  ElaborateSrc(ForwardUdpSrc("p_fwd u(, f_a, f_b);"), f, "fwd_top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a UDP instance's output terminal is left empty", 3,
                            "A.5.4"));
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpWithAnEmptyInputTerminal) {
  ElabFixture f;
  ElaborateSrc(ForwardUdpSrc("p_fwd u(f_out, , f_b);"), f, "fwd_top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a UDP instance's input terminal is left empty", 3,
                            "A.5.4"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "a UDP instance's output terminal is left empty",
                             3, "A.5.4"));
}

TEST(UdpInstanceElaboration, ForwardDeclaredUdpWithAnAttributedTerminal) {
  ElabFixture f;
  ElaborateSrc(ForwardUdpSrc("p_fwd u(f_out, (* keep *) f_a, f_b);"), f,
               "fwd_top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a UDP instance's terminal takes no attribute "
                            "instance",
                            3, "A.5.4"));
}

TEST(UdpInstanceElaboration, ModuleInstanceTakesAnAttributedConnection) {
  ElabFixture f;
  ElaborateSrc(
      "module m_child(output o, input i);\n"
      "endmodule\n"
      "module fwd_top;\n"
      "  wire f_out, f_a;\n"
      "  m_child u(f_out, (* keep *) f_a);\n"
      "endmodule\n",
      f, "fwd_top");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
