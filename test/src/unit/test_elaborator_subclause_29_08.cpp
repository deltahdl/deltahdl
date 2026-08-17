#include <cstdint>
#include <set>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

// §29.8 states what a UDP instantiation writes into the design. Syntax 29-2
// gives it as `udp_instantiation ::= udp_identifier [ drive_strength ]
// [ delay2 ] udp_instance { , udp_instance } ;` over `udp_instance ::=
// [ name_of_instance ] ( output_terminal , input_terminal
// { , input_terminal } )`, and the prose adds "The instance name is optional,
// just as for gates. The terminal connection order is as specified in the UDP
// definition. Only two delays may be specified because z is not supported for
// UDPs."
//
// Each case below elaborates one such instantiation and reads back the
// RtlirUdpInst (src/elaborator/rtlir.h:247) that
// Elaborator::ElaborateUdpInst (src/elaborator/elaborator_items_udp.cpp:198)
// appends to RtlirModule::udp_insts. The call stands at
// src/elaborator/elaborator_items.cpp:653, in the
// `case ModuleItemKind::kUdpInst:` arm of Elaborator::ElaborateDeclItem
// (src/elaborator/elaborator_items.cpp:608). Before #3197 that arm wrote
// nothing, so the instance drove no terminal and every assertion here would
// read an empty RtlirModule::udp_insts.

namespace {

// The top module of a design ElaborateSrc built, or nullptr when the elaborator
// rooted none. Each case names its own top, so a design that reached the
// assertions holds exactly that one.
RtlirModule* TopModule(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  return design->top_modules[0];
}

// §29.8: the instantiation is what drives the primitive's output terminal, so
// elaborating a module that instantiates a combinational primitive shall leave
// a driver behind naming the net the source connected first. This is the case
// #3197 was filed on: with the kUdpInst arm writing nothing,
// RtlirModule::udp_insts stayed empty and the net `q_out` had no driver at all.
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

// §29.8: `udp_instance ::= [ name_of_instance ] ( output_terminal ,
// input_terminal { , input_terminal } )` puts the output terminal first and
// "The terminal connection order is as specified in the UDP definition", so the
// terminal the source wrote first reaches RtlirUdpInst::output and the rest
// reach RtlirUdpInst::inputs in that order. The three terminals carry different
// identifiers, so an implementation that filled output from a later terminal or
// reversed the inputs reads back a different name here rather than the same
// one.
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

// §29.8: a UDP instantiation names the primitive it instantiates, so
// RtlirUdpInst::decl shall be the UdpDecl (src/parser/ast_specify.h:139) the
// source declared under that name and not merely some primitive. The
// assertions read UdpDecl::name and UdpDecl::output_name, which differ between
// the two primitives this source declares, so resolving the instance to the
// wrong declaration reads back `p_other1` rather than `p_named2`.
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

// §29.8 admits a drive_strength and a delay2 on an instantiation, ordering them
// in Syntax 29-2 as `udp_identifier [ drive_strength ] [ delay2 ] udp_instance`
// -- which is why the strength spec below stands between the primitive's name
// and the instance name rather than after it. Both reach the elaborated
// instance: the `#5` reaches RtlirUdpInst::delay and the
// `(strong1, weak0)` reaches RtlirUdpInst::drive_strength1 and
// RtlirUdpInst::drive_strength0. The strength codes are the ones
// Parser::ParseStrength0 (src/parser/parser_toplevel.cpp:291) and
// Parser::ParseStrength1 (src/parser/parser_toplevel.cpp:309) return, where
// strong is 4 and weak is 2; 0 is what an instantiation with no strength spec
// leaves, so neither value here is one an instance that dropped the spec could
// show.
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

// §29.8: "The instance name is optional, just as for gates", so an
// instantiation the source left unnamed still elaborates to an RtlirUdpInst,
// with RtlirUdpInst::name empty. The terminals are asserted alongside the empty
// name so the case cannot pass on an instance that was never recorded: an
// absent instance has no terminals to read either, and reading them is what
// separates "elaborated without a name" from "not elaborated".
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

// §29.8 covers the primitive instantiation only; §28.4 gives the `and` gate an
// output computed by an operator, which Elaborator::ElaborateDeclItem sends to
// ElaborateGateInst (src/elaborator/elaborator_gates.cpp:635) and which lands
// in RtlirModule::assigns as an RtlirContAssign whose lhs is the gate's first
// terminal. The two arms write to different members of the same RtlirModule, so
// a module holding one of each shall show one entry in each: a gate that leaked
// into RtlirModule::udp_insts, or a primitive that lowered to an
// RtlirContAssign, changes one of these counts.
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

// §29.8: "An optional range may be specified for an array of UDP instances",
// and "Instances of UDPs are specified inside modules in the same manner as
// gates (see 28.3)", so the four-element range below shall leave four entries
// in RtlirModule::udp_insts rather than one. §28.3.6 says which bit each
// element connects to: "If bit lengths are different, each instance shall get a
// part-select of the port expression, of a bit length equal to the instance
// port bit length", so the four elements take the four distinct bits of the
// 4-bit terminal `r_out_v`.
//
// Both assertions are needed. The count alone passes an expansion that
// connected the whole vector to all four instances, which is what the four
// instances of one unexpanded terminal would look like, and the set of bits
// alone passes a count of any size. The instance range is `[7:4]` and the
// terminal is declared `[3:0]` so that no array index is also a bit position:
// an implementation that used the instance's own index as the bit position
// reads back bits 4 through 7, which are not bits of this terminal at all.
//
// This is the case #3199 was filed on: with the kUdpInst arm returning without
// appending anything when the instance carries a range,
// RtlirModule::udp_insts is empty and no bit of `r_out_v` is driven.
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

// §29.8: "The terminal connection rules remain the same as outlined in 28.3.6",
// and §28.3.6 rules that "Too many or too few bits to connect to all the
// instances shall be considered an error". The array below has four elements,
// so its output terminal is either 1 bit and broadcast to each element or 4
// bits and distributed across them; the 3-bit `w_out_v` is neither, and the
// three surplus-or-missing bits connect to nothing.
//
// The report is named through ReportedError so the case cannot pass on some
// other rejection of this source -- an unexpanded array reports nothing at all
// today, and a source rejected for a different reason would satisfy a bare
// "were there errors" question.
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

}  // namespace
