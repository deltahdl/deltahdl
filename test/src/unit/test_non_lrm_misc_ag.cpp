// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- Elaborator resolves if_generate_construct (true branch) ---
TEST(ParserAnnexA042, ElaborationGenerateIfTrue) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter W = 16) ();\n"
      "  if (W > 8) begin\n"
      "    logic [15:0] wide_bus;\n"
      "  end else begin\n"
      "    logic [7:0] narrow_bus;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_wide = false;
  for (const auto& v : mod->variables) {
    if (v.name == "wide_bus") found_wide = true;
  }
  EXPECT_TRUE(found_wide);
}

// --- Elaborator resolves if_generate_construct (false/else branch) ---
TEST(ParserAnnexA042, ElaborationGenerateIfFalse) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter W = 4) ();\n"
      "  if (W > 8) begin\n"
      "    logic [15:0] wide_bus;\n"
      "  end else begin\n"
      "    logic [7:0] narrow_bus;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_narrow = false;
  for (const auto& v : mod->variables) {
    if (v.name == "narrow_bus") found_narrow = true;
  }
  EXPECT_TRUE(found_narrow);
}

// --- Elaborator resolves case_generate_construct ---
TEST(ParserAnnexA042, ElaborationGenerateCase) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter SEL = 1) ();\n"
      "  case (SEL)\n"
      "    0: logic [7:0] bus0;\n"
      "    1: logic [15:0] bus1;\n"
      "    default: logic [31:0] bus_def;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_bus1 = false;
  for (const auto& v : mod->variables) {
    if (v.name == "bus1") found_bus1 = true;
  }
  EXPECT_TRUE(found_bus1);
}

// --- Elaborator resolves case_generate_construct (default branch) ---
TEST(ParserAnnexA042, ElaborationGenerateCaseDefault) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter SEL = 99) ();\n"
      "  case (SEL)\n"
      "    0: logic [7:0] bus0;\n"
      "    1: logic [15:0] bus1;\n"
      "    default: logic [31:0] bus_def;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  bool found_def = false;
  for (const auto& v : mod->variables) {
    if (v.name == "bus_def") found_def = true;
  }
  EXPECT_TRUE(found_def);
}

// --- Elaborator expands for-generate with module instantiation ---
TEST(ParserAnnexA042, ElaborationGenerateForModuleInst) {
  ElabFixture f;
  auto* design = Elaborate(
      "module sub(input logic a); endmodule\n"
      "module top #(parameter N = 2) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin : blk\n"
      "      sub u(.a(1'b0));\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->children.size(), 2u);
}

// =============================================================================
// A.5 -- UDP declarations
// =============================================================================
TEST(ParserAnnexA, A5UdpCombinational) {
  auto r = Parse(
      "primitive mux2(output y, input a, input b, input s);\n"
      "  table\n"
      "    0 ? 0 : 0 ;\n"
      "    1 ? 0 : 1 ;\n"
      "    ? 0 1 : 0 ;\n"
      "    ? 1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "mux2");
  EXPECT_FALSE(r.cu->udps[0]->is_sequential);
}

TEST(ParserAnnexA, A5UdpSequential) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0 ;\n"
      "    1 r : ? : 1 ;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);
}

// =============================================================================
// A.5.1 -- UDP declaration
//
// udp_nonansi_declaration ::=
//   { attribute_instance } primitive udp_identifier ( udp_port_list ) ;
//
// udp_ansi_declaration ::=
//   { attribute_instance } primitive udp_identifier
//     ( udp_declaration_port_list ) ;
//
// udp_declaration ::=
//   udp_nonansi_declaration udp_port_declaration { udp_port_declaration }
//     udp_body endprimitive [ : udp_identifier ]
//   | udp_ansi_declaration udp_body
//     endprimitive [ : udp_identifier ]
//   | extern udp_nonansi_declaration
//   | extern udp_ansi_declaration
//   | { attribute_instance } primitive udp_identifier ( . * ) ;
//     { udp_port_declaration } udp_body
//     endprimitive [ : udp_identifier ]
// =============================================================================
// --- udp_ansi_declaration: combinational ---
TEST(ParserAnnexA051, AnsiCombinational) {
  auto r = Parse(
      "primitive and_gate(output out, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "and_gate");
  EXPECT_EQ(udp->output_name, "out");
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->input_names.size(), 2u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  ASSERT_EQ(udp->table.size(), 4u);
}

// --- udp_ansi_declaration: sequential (output reg) ---
TEST(ParserAnnexA051, AnsiSequential) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "dff");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->output_name, "q");
  ASSERT_EQ(udp->input_names.size(), 2u);
  ASSERT_EQ(udp->table.size(), 2u);
}

}  // namespace
