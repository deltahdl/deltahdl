#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

RtlirDesign* Elaborate(const std::string& src, ElabFixture& f,
                       std::string_view top = "") {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto name = top.empty() ? cu->modules.back()->name : top;
  return elab.Elaborate(name);
}

}  // namespace

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

// NOLINTNEXTLINE(readability-function-cognitive-complexity)
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
  bool found_for = false, found_if = false, found_case = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found_for = true;
    if (item->kind == ModuleItemKind::kGenerateIf) found_if = true;
    if (item->kind == ModuleItemKind::kGenerateCase) found_case = true;
  }
  EXPECT_TRUE(found_for);
  EXPECT_TRUE(found_if);
  EXPECT_TRUE(found_case);
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
