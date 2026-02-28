// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

bool HasItemOfKind(const std::vector<ModuleItem*>& items, ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

namespace {

// --- named_checker_port_connection: .port_identifier(property_actual_arg) ---
TEST(ParserAnnexA0414, CheckerInstNamedPorts) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n"
      "module m; my_chk u0(.clk(clk), .rst(rst)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

// --- named_checker_port_connection: .port_identifier (no parentheses) ---
TEST(ParserAnnexA0414, CheckerInstNamedPortNoParens) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n"
      "module m; my_chk u0(.clk, .rst); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

// --- named_checker_port_connection: .* (wildcard) ---
TEST(ParserAnnexA0414, CheckerInstWildcardPort) {
  auto r = Parse(
      "checker my_chk(input logic clk);\n"
      "endchecker\n"
      "module m; my_chk u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

// --- list_of_checker_port_connections: empty ---
TEST(ParserAnnexA0414, CheckerInstEmptyPorts) {
  auto r = Parse(
      "checker my_chk;\n"
      "endchecker\n"
      "module m; my_chk u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_ports.empty());
}

// --- name_of_instance: with unpacked_dimension (instance array) ---
TEST(ParserAnnexA0414, CheckerInstArray) {
  auto r = Parse(
      "checker my_chk(input logic clk);\n"
      "endchecker\n"
      "module m; my_chk u0 [3:0] (.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_chk");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

// --- checker_instantiation: inside another checker ---
TEST(ParserAnnexA0414, CheckerInstInsideChecker) {
  auto r = Parse(
      "checker inner_chk(input logic sig);\n"
      "endchecker\n"
      "checker outer_chk;\n"
      "  logic sig;\n"
      "  inner_chk u0(.sig(sig));\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 2u);
  ASSERT_GE(r.cu->checkers[1]->items.size(), 2u);
  auto* inst = r.cu->checkers[1]->items[1];
  EXPECT_EQ(inst->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(inst->inst_module, "inner_chk");
  EXPECT_EQ(inst->inst_name, "u0");
}

// =============================================================================
// Elaboration tests -- checker instantiation resolved through elaborator
// =============================================================================
// --- Elaborator resolves checker instantiation within a module ---
TEST(ParserAnnexA0414, ElaborationCheckerInstInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk, rst;\n"
      "  my_chk u0(.clk(clk), .rst(rst));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "my_chk");
  EXPECT_EQ(top->children[0].inst_name, "u0");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

// --- Elaborator resolves checker instantiation with port bindings ---
TEST(ParserAnnexA0414, ElaborationCheckerInstPortBindings) {
  ElabFixture f;
  auto* design = Elaborate(
      "checker simple_chk(input logic data);\n"
      "endchecker\n"
      "module top;\n"
      "  logic d;\n"
      "  simple_chk u0(.data(d));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_GE(top->children[0].port_bindings.size(), 1u);
  EXPECT_EQ(top->children[0].port_bindings[0].port_name, "data");
}

// --- Elaborator resolves checker inside checker ---
TEST(ParserAnnexA0414, ElaborationCheckerInsideChecker) {
  ElabFixture f;
  auto* design = Elaborate(
      "checker inner_chk(input logic sig);\n"
      "endchecker\n"
      "checker outer_chk;\n"
      "  logic sig;\n"
      "  inner_chk u0(.sig(sig));\n"
      "endchecker\n"
      "module top;\n"
      "  outer_chk oi();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "outer_chk");
  auto* outer = top->children[0].resolved;
  ASSERT_NE(outer, nullptr);
  ASSERT_GE(outer->children.size(), 1u);
  EXPECT_EQ(outer->children[0].module_name, "inner_chk");
  EXPECT_NE(outer->children[0].resolved, nullptr);
}

// =============================================================================
// A.4.2 -- Generated instantiation
//
// generate_region ::= generate { generate_item } endgenerate
//
// loop_generate_construct ::=
//   for ( genvar_initialization ; genvar_expression ; genvar_iteration )
//     generate_block
//
// genvar_initialization ::= [ genvar ] genvar_identifier = constant_expression
//
// genvar_iteration ::=
//   genvar_identifier assignment_operator genvar_expression
//   | inc_or_dec_operator genvar_identifier
//   | genvar_identifier inc_or_dec_operator
//
// conditional_generate_construct ::=
//   if_generate_construct | case_generate_construct
//
// if_generate_construct ::=
//   if ( constant_expression ) generate_block [ else generate_block ]
//
// case_generate_construct ::=
//   case ( constant_expression ) case_generate_item { case_generate_item }
//     endcase
//
// case_generate_item ::=
//   constant_expression { , constant_expression } : generate_block
//   | default [ : ] generate_block
//
// generate_block ::=
//   generate_item
//   | [ generate_block_identifier : ] begin [ : generate_block_identifier ]
//       { generate_item } end [ : generate_block_identifier ]
//
// generate_item ::=
//   module_or_generate_item
//   | interface_or_generate_item
//   | checker_or_generate_item
// =============================================================================
// --- generate_region: basic ---
TEST(ParserAnnexA042, GenerateRegionBasic) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->items.size(), 1u);
}

// --- generate_region: empty ---
TEST(ParserAnnexA042, GenerateRegionEmpty) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

// --- generate_region: multiple generate_items ---
TEST(ParserAnnexA042, GenerateRegionMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire a;\n"
      "    wire b;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

// --- loop_generate_construct: basic for loop ---
TEST(ParserAnnexA042, LoopGenerateBasic) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i = i + 1) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_init, nullptr);
  ASSERT_NE(gen->gen_cond, nullptr);
  ASSERT_NE(gen->gen_step, nullptr);
  ASSERT_EQ(gen->gen_body.size(), 1u);
}

// --- genvar_initialization: with inline genvar keyword ---
TEST(ParserAnnexA042, GenvarInitWithGenvarKeyword) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i = i + 1) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_init, nullptr);
}

// --- genvar_initialization: without genvar keyword (pre-declared) ---
TEST(ParserAnnexA042, GenvarInitWithoutGenvarKeyword) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found = true;
  }
  EXPECT_TRUE(found);
}

// --- genvar_iteration: assignment_operator (i = i + 1) ---
TEST(ParserAnnexA042, GenvarIterationAssignment) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i = i + 1) begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_NE(gen->gen_step, nullptr);
}

// --- genvar_iteration: compound assignment_operator (i += 1) ---
TEST(ParserAnnexA042, GenvarIterationCompoundAssign) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i += 1) begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_NE(gen->gen_step, nullptr);
}

// --- genvar_iteration: genvar_identifier inc_or_dec_operator (i++) ---
TEST(ParserAnnexA042, GenvarIterationPostIncrement) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_NE(gen->gen_step, nullptr);
}

// --- genvar_iteration: genvar_identifier dec_operator (i--) ---
TEST(ParserAnnexA042, GenvarIterationPostDecrement) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 3; i >= 0; i--) begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_NE(gen->gen_step, nullptr);
}

// --- if_generate_construct: basic if ---
TEST(ParserAnnexA042, IfGenerateBasic) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1)\n"
      "    assign out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_else, nullptr);
}

// --- if_generate_construct: if with else ---
TEST(ParserAnnexA042, IfGenerateWithElse) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1)\n"
      "    assign out = a;\n"
      "  else\n"
      "    assign out = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else, nullptr);
  ASSERT_EQ(gen->gen_else->gen_body.size(), 1u);
}

// --- if_generate_construct: if / else-if / else chain ---
TEST(ParserAnnexA042, IfGenerateElseIfChain) {
  auto r = Parse(
      "module m;\n"
      "  if (W == 1)\n"
      "    assign out = a;\n"
      "  else if (W == 2)\n"
      "    assign out = b;\n"
      "  else\n"
      "    assign out = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else, nullptr);
  EXPECT_EQ(gen->gen_else->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else->gen_else, nullptr);
}

// --- case_generate_construct: basic case ---
TEST(ParserAnnexA042, CaseGenerateBasic) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8: assign out = in8;\n"
      "    16: assign out = in16;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(gen->gen_case_items.size(), 2u);
  EXPECT_FALSE(gen->gen_case_items[0].is_default);
  EXPECT_FALSE(gen->gen_case_items[1].is_default);
}

// --- case_generate_item: default ---
TEST(ParserAnnexA042, CaseGenerateWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8: assign out = in8;\n"
      "    default: assign out = in_def;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_case_items.size(), 2u);
  EXPECT_FALSE(gen->gen_case_items[0].is_default);
  EXPECT_TRUE(gen->gen_case_items[1].is_default);
}

// --- case_generate_item: multiple patterns ---
TEST(ParserAnnexA042, CaseGenerateMultiplePatterns) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8, 16: assign out = narrow;\n"
      "    32, 64: assign out = wide;\n"
      "    default: assign out = other;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_case_items.size(), 3u);
  EXPECT_EQ(gen->gen_case_items[0].patterns.size(), 2u);
  EXPECT_EQ(gen->gen_case_items[1].patterns.size(), 2u);
  EXPECT_TRUE(gen->gen_case_items[2].is_default);
}

// --- generate_block: single generate_item (no begin/end) ---
TEST(ParserAnnexA042, GenerateBlockSingleItem) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++)\n"
      "    assign out[i] = in[i];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
}

// --- generate_block: begin/end with label ---
TEST(ParserAnnexA042, GenerateBlockLabeled) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : gen_blk\n"
      "    assign out[i] = in[i];\n"
      "  end : gen_blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
}

// --- generate_block: begin/end with multiple items ---
TEST(ParserAnnexA042, GenerateBlockMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  if (W > 0) begin\n"
      "    wire a;\n"
      "    assign a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  EXPECT_GE(gen->gen_body.size(), 2u);
}

// --- generate_item: module_or_generate_item (module instantiation) ---
TEST(ParserAnnexA042, GenerateItemModuleInst) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : blk\n"
      "    sub u(.a(in[i]), .b(out[i]));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

// --- generate_item: module_or_generate_item (always block) ---
TEST(ParserAnnexA042, GenerateItemAlwaysBlock) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : blk\n"
      "    always @(posedge clk) q[i] <= d[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kAlwaysBlock);
}

// --- generate_item: interface_or_generate_item (generate in interface) ---
TEST(ParserAnnexA042, GenerateItemInInterface) {
  auto r = Parse(
      "interface my_if;\n"
      "  if (W > 0)\n"
      "    wire a;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  bool found_if = false;
  for (auto* item : r.cu->interfaces[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) found_if = true;
  }
  EXPECT_TRUE(found_if);
}

// --- generate_item: checker_or_generate_item (generate in checker) ---
TEST(ParserAnnexA042, GenerateItemInChecker) {
  auto r = Parse(
      "checker my_chk;\n"
      "  if (W > 0)\n"
      "    wire a;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  bool found_if = false;
  for (auto* item : r.cu->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) found_if = true;
  }
  EXPECT_TRUE(found_if);
}

// --- nested generate constructs: for inside if ---
TEST(ParserAnnexA042, NestedForInsideIf) {
  auto r = Parse(
      "module m;\n"
      "  if (USE_PIPELINE) begin\n"
      "    for (genvar i = 0; i < STAGES; i++) begin : stage\n"
      "      assign pipe[i] = data[i];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_GE(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kGenerateFor);
}

// --- nested generate constructs: for inside for ---
TEST(ParserAnnexA042, NestedForInsideFor) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i++) begin : outer\n"
      "    for (genvar j = 0; j < 2; j++) begin : inner\n"
      "      assign out[i][j] = in[i][j];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* outer = r.cu->modules[0]->items[0];
  EXPECT_EQ(outer->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(outer->gen_body.size(), 1u);
  EXPECT_EQ(outer->gen_body[0]->kind, ModuleItemKind::kGenerateFor);
}

// --- generate_region with mixed constructs ---
TEST(ParserAnnexA042, GenerateRegionMixedConstructs) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 2; i++) begin\n"
      "      wire w;\n"
      "    end\n"
      "    if (W > 0)\n"
      "      wire a;\n"
      "    case (SEL)\n"
      "      0: wire x;\n"
      "      default: wire y;\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(HasItemOfKind(mod->items, ModuleItemKind::kGenerateFor));
  EXPECT_TRUE(HasItemOfKind(mod->items, ModuleItemKind::kGenerateIf));
  EXPECT_TRUE(HasItemOfKind(mod->items, ModuleItemKind::kGenerateCase));
}

// =============================================================================
// Elaboration tests -- generate constructs resolved through elaborator
// =============================================================================
// --- Elaborator expands loop_generate_construct ---
TEST(ParserAnnexA042, ElaborationGenerateForExpansion) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter N = 3) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[0].name, "i_0_x");
  EXPECT_EQ(mod->variables[1].name, "i_1_x");
  EXPECT_EQ(mod->variables[2].name, "i_2_x");
}

// --- Elaborator handles zero-iteration loop ---
TEST(ParserAnnexA042, ElaborationGenerateForZeroIter) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter N = 0) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 0u);
}

// --- Elaborator expands for-generate with continuous assigns ---
TEST(ParserAnnexA042, ElaborationGenerateForWithAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter N = 2) ();\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [31:0] w;\n"
      "      assign w = 100;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->assigns.size(), 2u);
}

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
