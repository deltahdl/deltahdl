// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =========================================================================
// LRM section 23.4: Nested modules
// =========================================================================
TEST(ParserSection23, NestedModuleParsesOk) {
  EXPECT_TRUE(
      ParseOk("module outer;\n"
              "  wire w;\n"
              "  module inner;\n"
              "    assign w = 1'b1;\n"
              "  endmodule\n"
              "  inner i1();\n"
              "endmodule\n"));
}

TEST(ParserSection23, NestedModuleMultiple) {
  EXPECT_TRUE(
      ParseOk("module outer(input d, ck, output q, nq);\n"
              "  wire q1, nq1;\n"
              "  module ff1;\n"
              "    nand g1(nq1, d, q1);\n"
              "  endmodule\n"
              "  ff1 i1();\n"
              "  module ff2;\n"
              "    nand g2(q1, ck, nq1);\n"
              "  endmodule\n"
              "  ff2 i2();\n"
              "endmodule\n"));
}

// =========================================================================
// LRM section 27.3: Generate construct syntax / generate regions
// =========================================================================
TEST(ParserSection23, GenerateRegionWithFor) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 4; i = i + 1) begin : blk\n"
      "      assign a[i] = b[i];\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(ParserSection23, GenerateRegionWithIf) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    if (WIDTH > 8) begin : wide\n"
      "      assign a = b;\n"
      "    end else begin : narrow\n"
      "      assign a = c;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) found = true;
  }
  EXPECT_TRUE(found);
}

// =========================================================================
// LRM section 27.3: Generate block syntax (begin/end with labels)
// =========================================================================
TEST(ParserSection23, GenerateBlockNamedBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen_blk\n"
      "    wire w;\n"
      "    assign w = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) {
      found = true;
      EXPECT_FALSE(item->gen_body.empty());
    }
  }
  EXPECT_TRUE(found);
}

// =========================================================================
// LRM section 27.5: Conditional generates (if-generate)
// =========================================================================
TEST(ParserSection23, IfGenerateWithElseIf) {
  auto r = Parse(
      "module m;\n"
      "  if (W == 8) begin : w8\n"
      "    assign a = b;\n"
      "  end else if (W == 16) begin : w16\n"
      "    assign a = c;\n"
      "  end else begin : wother\n"
      "    assign a = d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(item->gen_cond, nullptr);
  EXPECT_FALSE(item->gen_body.empty());
  ASSERT_NE(item->gen_else, nullptr);
  EXPECT_NE(item->gen_else->gen_cond, nullptr);
  ASSERT_NE(item->gen_else->gen_else, nullptr);
}

TEST(ParserSection23, IfGenerateNoElse) {
  auto r = Parse(
      "module m;\n"
      "  if (EN) begin\n"
      "    assign out = in;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(item->gen_cond, nullptr);
  EXPECT_EQ(item->gen_else, nullptr);
}

TEST(ParserSection23, IfGenerateSingleItemNoBegin) {
  auto r = Parse(
      "module m;\n"
      "  if (EN)\n"
      "    assign out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateIf);
  EXPECT_EQ(item->gen_body.size(), 1);
}

// =========================================================================
// LRM section 27.4: Loop generates
// =========================================================================
TEST(ParserSection23, LoopGenerateForStructure) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 8; i = i + 1) begin : bits\n"
      "    assign out[i] = ^in[7:i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = FindItemByKind(r, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen, nullptr);
  EXPECT_NE(gen->gen_init, nullptr);
  EXPECT_NE(gen->gen_cond, nullptr);
  EXPECT_NE(gen->gen_step, nullptr);
  EXPECT_FALSE(gen->gen_body.empty());
}

TEST(ParserSection23, LoopGenerateInlineGenvar) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
      "    assign a[i] = b[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = FindItemByKind(r, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen, nullptr);
  EXPECT_NE(gen->gen_init, nullptr);
}

TEST(ParserSection23, LoopGenerateWithModuleInst) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : stage\n"
      "    sub u (.a(in[i]), .b(out[i]));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = FindItemByKind(r, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen, nullptr);
  ASSERT_EQ(gen->gen_body.size(), 1);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

// =========================================================================
// LRM section 27.4: Genvar declarations
// =========================================================================
TEST(ParserSection23, GenvarDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(mod->items[0]->name, "i");
}

TEST(ParserSection23, GenvarMultipleDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  genvar i, j, k;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 3);
  EXPECT_EQ(mod->items[0]->name, "i");
  EXPECT_EQ(mod->items[1]->name, "j");
  EXPECT_EQ(mod->items[2]->name, "k");
}

// =========================================================================
// LRM section 27.4: Genvar expressions in loop generate
// =========================================================================
TEST(ParserSection23, GenvarExprInLoopBound) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2 * N; i = i + 2) begin : evens\n"
      "    assign a[i] = b[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ModuleItem* gen = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) gen = item;
  }
  ASSERT_NE(gen, nullptr);
  EXPECT_NE(gen->gen_cond, nullptr);
  EXPECT_NE(gen->gen_step, nullptr);
}

TEST(ParserSection23, GenvarPostIncrementStep) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  for (genvar i = 0; i < 4; i++) begin : blk\n"
              "    assign a[i] = b[i];\n"
              "  end\n"
              "endmodule\n"));
}

// =========================================================================
// LRM section 27.4: Indexed generate block names
// =========================================================================
TEST(ParserSection23, IndexedGenerateBlockName) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : stage\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ModuleItem* gen = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) gen = item;
  }
  ASSERT_NE(gen, nullptr);
  EXPECT_FALSE(gen->gen_body.empty());
}

TEST(ParserSection23, EndLabelOnGenerateBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  genvar i;\n"
              "  for (i = 0; i < 4; i = i + 1) begin : blk\n"
              "    assign a[i] = b[i];\n"
              "  end : blk\n"
              "endmodule\n"));
}

TEST(ParserSection23, CaseGenerateMultipleLabels) {
  auto r = Parse(
      "module m;\n"
      "  case (SEL)\n"
      "    0, 1: assign a = b;\n"
      "    2, 3: assign a = c;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(item->gen_case_items.size(), 2);
  EXPECT_EQ(item->gen_case_items[0].patterns.size(), 2);
  EXPECT_EQ(item->gen_case_items[1].patterns.size(), 2);
}

// =========================================================================
// LRM section 23.5: Extern modules
// =========================================================================
TEST(ParserSection23, ExternModuleNonAnsiPorts) {
  auto r = Parse("extern module m (a, b, c);\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  EXPECT_TRUE(mod->is_extern);
  EXPECT_TRUE(mod->items.empty());
}

TEST(ParserSection23, ExternModuleWithParams) {
  auto r = Parse(
      "extern module a #(parameter size = 8)\n"
      "  (input [size:0] x, output logic y);\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "a");
  EXPECT_TRUE(mod->is_extern);
  ASSERT_EQ(mod->params.size(), 1);
  EXPECT_EQ(mod->params[0].first, "size");
  ASSERT_EQ(mod->ports.size(), 2);
}

TEST(ParserSection23, ExternModuleFollowedByDefinition) {
  auto r = Parse(
      "extern module ext (input a, output b);\n"
      "module other (input x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 2);
  EXPECT_EQ(r.cu->modules[0]->name, "ext");
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_EQ(r.cu->modules[1]->name, "other");
  EXPECT_FALSE(r.cu->modules[1]->is_extern);
}

// =========================================================================
// Combined / integration tests
// =========================================================================
TEST(ParserSection23, ParameterizedModuleWithGenerate) {
  auto r = Parse(
      "module gray2bin #(parameter SIZE = 8) (\n"
      "  output [SIZE-1:0] bin,\n"
      "  input [SIZE-1:0] gray);\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < SIZE; i = i + 1) begin : bitnum\n"
      "      assign bin[i] = ^gray[SIZE-1:i];\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "gray2bin");
  ASSERT_EQ(mod->params.size(), 1);
  EXPECT_EQ(mod->params[0].first, "SIZE");
  ASSERT_EQ(mod->ports.size(), 2);
}

TEST(ParserSection23, GenerateNestedLoops) {
  auto r = Parse(
      "module m;\n"
      "  genvar i, j;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : B1\n"
      "    for (j = 0; j < 2; j = j + 1) begin : B2\n"
      "      assign a[i][j] = b[i][j];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ModuleItem* outer = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) outer = item;
  }
  ASSERT_NE(outer, nullptr);
  bool has_inner = false;
  for (auto* inner : outer->gen_body) {
    if (inner->kind == ModuleItemKind::kGenerateFor) has_inner = true;
  }
  EXPECT_TRUE(has_inner);
}

TEST(ParserSection23, GenerateIfInsideForLoop) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : blk\n"
      "    if (i > 0) begin : guard\n"
      "      assign a[i] = b[i-1];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ModuleItem* gen = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) gen = item;
  }
  ASSERT_NE(gen, nullptr);
  bool has_if = false;
  for (auto* inner : gen->gen_body) {
    if (inner->kind == ModuleItemKind::kGenerateIf) has_if = true;
  }
  EXPECT_TRUE(has_if);
}

// =============================================================================
// LRM section 23.2.2 -- Port declarations
// =============================================================================
// --- ANSI style ports ---
TEST(ParserSection23, Sec23_2_2_AnsiPortDirections) {
  // All four port directions: input, output, inout, ref
  auto r = Parse(
      "module m (input logic a, output logic y,\n"
      "          inout wire [7:0] data, ref logic [3:0] r);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "y");
  EXPECT_EQ(r.cu->modules[0]->ports[2].direction, Direction::kInout);
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "data");
  EXPECT_EQ(r.cu->modules[0]->ports[3].direction, Direction::kRef);
  EXPECT_EQ(r.cu->modules[0]->ports[3].name, "r");
}

TEST(ParserSection23, Sec23_2_2_NonAnsiPortDeclarations) {
  // Non-ANSI style: port list + separate direction declarations
  auto r = Parse(
      "module m (a, b, y);\n"
      "  input a, b;\n"
      "  output y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  // Variants with packed types and inout
  EXPECT_TRUE(
      ParseOk("module m (a, d); input [15:0] a; inout [7:0] d; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m (a, b); inout [7:0] a; inout [7:0] b; endmodule\n"));
}

// --- Empty port list ---
TEST(ParserSection23, Sec23_2_2_EmptyPortsAndMiscVariants) {
  auto r1 = Parse("module m (); endmodule\n");
  ASSERT_NE(r1.cu, nullptr);
  EXPECT_FALSE(r1.has_errors);
  EXPECT_EQ(r1.cu->modules[0]->ports.size(), 0u);
  auto r2 = Parse("module m; endmodule\n");
  ASSERT_NE(r2.cu, nullptr);
  EXPECT_FALSE(r2.has_errors);
  EXPECT_EQ(r2.cu->modules[0]->ports.size(), 0u);
  EXPECT_TRUE(ParseOk("module m (.*); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (input int x = 10); endmodule\n"));
  // ANSI port type variants
  EXPECT_TRUE(ParseOk("module m (input var int in1); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (output reg [7:0] q); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (input signed [7:0] s); endmodule\n"));
  // macromodule is interchangeable with module (LRM 23.2)
  EXPECT_TRUE(ParseOk("macromodule mm; endmodule\n"));
}

using ProgramParseTest = ProgramTestParse;

// =============================================================================
// §24.1 Basic program declarations
// =============================================================================
TEST_F(ProgramParseTest, EmptyProgram) {
  auto* unit = Parse("program p; endprogram");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  EXPECT_TRUE(unit->programs[0]->ports.empty());
  EXPECT_TRUE(unit->programs[0]->params.empty());
  EXPECT_TRUE(unit->programs[0]->items.empty());
}

TEST_F(ProgramParseTest, ProgramWithEndLabel) {
  auto* unit = Parse("program p; endprogram : p");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

// =============================================================================
// §24.2 Program ports and parameters
// =============================================================================
TEST_F(ProgramParseTest, ProgramWithPorts) {
  auto* unit = Parse(
      "program p(input logic clk, input logic rst);\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_GE(unit->programs[0]->ports.size(), 2u);
  EXPECT_EQ(unit->programs[0]->ports[0].name, "clk");
  EXPECT_EQ(unit->programs[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(unit->programs[0]->ports[1].name, "rst");
  EXPECT_EQ(unit->programs[0]->ports[1].direction, Direction::kInput);
}

TEST_F(ProgramParseTest, ProgramWithParameters) {
  auto* unit = Parse(
      "program p #(parameter N = 8)(input logic clk);\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_EQ(unit->programs[0]->params.size(), 1u);
  EXPECT_EQ(unit->programs[0]->params[0].first, "N");
  ASSERT_GE(unit->programs[0]->ports.size(), 1u);
  EXPECT_EQ(unit->programs[0]->ports[0].name, "clk");
}

// =============================================================================
// §24.3 Program body items
// =============================================================================
TEST_F(ProgramParseTest, ProgramWithInitialBlock) {
  auto* unit = Parse(
      "program p;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST_F(ProgramParseTest, ProgramWithMultipleItems) {
  auto* unit = Parse(
      "program p;\n"
      "  logic [7:0] data;\n"
      "  assign data = 8'hFF;\n"
      "  initial begin\n"
      "    $display(\"test\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_GE(unit->programs[0]->items.size(), 3u);
}

TEST_F(ProgramParseTest, ProgramWithImportStatement) {
  auto* unit = Parse(
      "program p;\n"
      "  import pkg::*;\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(unit->programs[0]->items[0]->import_item.package_name, "pkg");
  EXPECT_TRUE(unit->programs[0]->items[0]->import_item.is_wildcard);
}

// =============================================================================
// §24.4 Multiple programs and coexistence with modules
// =============================================================================
TEST_F(ProgramParseTest, ProgramCoexistsWithModule) {
  auto* unit = Parse(
      "module m;\n"
      "endmodule\n"
      "program p;\n"
      "endprogram\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->modules[0]->name, "m");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST_F(ProgramParseTest, MultipleProgramsInCompilationUnit) {
  auto* unit = Parse(
      "program p1;\n"
      "endprogram\n"
      "program p2;\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 2u);
  EXPECT_EQ(unit->programs[0]->name, "p1");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  EXPECT_EQ(unit->programs[1]->name, "p2");
  EXPECT_EQ(unit->programs[1]->decl_kind, ModuleDeclKind::kProgram);
}

// =============================================================================
// §24.5 Program lifetime qualifier
// =============================================================================
TEST_F(ProgramParseTest, ProgramWithAutomaticLifetime) {
  auto* unit = Parse("program automatic p; endprogram");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

// =============================================================================
// §24.6 Program with task and function declarations
// =============================================================================
TEST_F(ProgramParseTest, ProgramWithTaskDecl) {
  auto* unit = Parse(
      "program p;\n"
      "  task run;\n"
      "    $display(\"running\");\n"
      "  endtask\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_GE(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(unit->programs[0]->items[0]->name, "run");
}

TEST_F(ProgramParseTest, ProgramWithFunctionDecl) {
  auto* unit = Parse(
      "program p;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_GE(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(unit->programs[0]->items[0]->name, "add");
}

TEST_F(ProgramParseTest, ProgramWithTaskAndFunction) {
  auto* unit = Parse(
      "program p;\n"
      "  task run;\n"
      "    $display(\"running\");\n"
      "  endtask\n"
      "  function int get_val;\n"
      "    return 42;\n"
      "  endfunction\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_GE(unit->programs[0]->items.size(), 2u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(unit->programs[0]->items[1]->kind, ModuleItemKind::kFunctionDecl);
}

// Returns true if any item in the list matches the given kind.
bool HasItemKind(const std::vector<ModuleItem*>& items, ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// Returns true if any item matches the given kind and name.
bool HasItemKindNamed(const std::vector<ModuleItem*>& items,
                      ModuleItemKind kind, std::string_view name) {
  for (auto* item : items) {
    if (item->kind == kind && item->name == name) return true;
  }
  return false;
}

// =============================================================================
// A.1.7 Program items
// =============================================================================
// program_item ::= port_declaration ;
TEST(SourceText, ProgramItemPortDecl) {
  auto r = Parse(
      "program prg(input logic clk, output logic done);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  auto* p = r.cu->programs[0];
  EXPECT_EQ(p->name, "prg");
  EXPECT_EQ(p->ports.size(), 2u);
  EXPECT_EQ(p->ports[0].direction, Direction::kInput);
  EXPECT_EQ(p->ports[1].direction, Direction::kOutput);
}

// non_port_program_item ::= continuous_assign
TEST(SourceText, ProgramContinuousAssign) {
  auto r = Parse(
      "program prg;\n"
      "  logic a, b;\n"
      "  assign a = b;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kContAssign));
}

// non_port_program_item ::= module_or_generate_item_declaration
TEST(SourceText, ProgramModuleOrGenerateItemDecl) {
  auto r = Parse(
      "program prg;\n"
      "  int count;\n"
      "  function void compute(); endfunction\n"
      "  task run(); endtask\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  auto& items = r.cu->programs[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "count"));
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kFunctionDecl, "compute"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kTaskDecl, "run"));
}

// non_port_program_item ::= initial_construct
TEST(SourceText, ProgramInitialConstruct) {
  auto r = Parse(
      "program prg;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

// non_port_program_item ::= final_construct
TEST(SourceText, ProgramFinalConstruct) {
  auto r = Parse(
      "program prg;\n"
      "  final begin\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kFinalBlock));
}

// non_port_program_item ::= concurrent_assertion_item
TEST(SourceText, ProgramConcurrentAssertion) {
  auto r = Parse(
      "program prg;\n"
      "  logic clk, a;\n"
      "  assert property (@(posedge clk) a);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kAssertProperty));
}

// non_port_program_item ::= timeunits_declaration
TEST(SourceText, ProgramTimeunitsDecl) {
  auto r = Parse(
      "program prg;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "prg");
}

// program_generate_item ::= loop_generate_construct
TEST(SourceText, ProgramGenerateLoop) {
  auto r = Parse(
      "program prg;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : blk\n"
      "    int x;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kGenerateFor));
}

// program_generate_item ::= conditional_generate_construct
TEST(SourceText, ProgramGenerateConditional) {
  auto r = Parse(
      "program prg;\n"
      "  parameter P = 1;\n"
      "  if (P) begin : blk\n"
      "    int x;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kGenerateIf));
}

// program_generate_item ::= generate_region
TEST(SourceText, ProgramGenerateRegion) {
  auto r = Parse(
      "program prg;\n"
      "  generate\n"
      "    int x;\n"
      "  endgenerate\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_FALSE(r.cu->programs[0]->items.empty());
}

// program_generate_item ::= elaboration_severity_system_task
TEST(SourceText, ProgramElabSeverityTask) {
  auto r = Parse(
      "program prg;\n"
      "  $info(\"program loaded\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kElabSystemTask));
}

// Combined: program with multiple A.1.7 item types.
TEST(SourceText, ProgramMultipleItemTypes) {
  auto r = Parse(
      "program prg(input logic clk);\n"
      "  timeunit 1ns;\n"
      "  int count;\n"
      "  assign count = 0;\n"
      "  initial begin $display(\"start\"); end\n"
      "  final begin $display(\"end\"); end\n"
      "  assert property (@(posedge clk) count >= 0);\n"
      "  generate int g; endgenerate\n"
      "  $warning(\"check\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  auto& items = r.cu->programs[0]->items;
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kVarDecl));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kContAssign));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kAssertProperty));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kElabSystemTask));
}

// 17. Program block with declarations
TEST(ParserClause03, Cl3_13_ProgramBlockWithDeclarations) {
  auto r = Parse(
      "program test_prog;\n"
      "  int count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test_prog");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  EXPECT_FALSE(r.cu->programs[0]->items.empty());
}

// description: program_declaration
TEST(SourceText, DescriptionProgram) {
  auto r = Parse("program prg; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "prg");
}

// =============================================================================
// A.1.2 program_declaration — all forms
// =============================================================================
// Program with lifetime.
TEST(SourceText, ProgramWithLifetime) {
  auto r = Parse("program automatic prg; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
}

// Program with end label.
TEST(SourceText, ProgramEndLabel) {
  auto r = Parse("program prg; endprogram : prg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Extern program declaration.
TEST(SourceText, ExternProgram) {
  auto r = Parse("extern program prg(input logic clk);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->is_extern);
  EXPECT_EQ(r.cu->programs[0]->name, "prg");
}

// =============================================================================
// A.1.2 program_declaration — all 5 forms
// =============================================================================
// Program with ANSI ports.
TEST(SourceText, ProgramAnsiHeader) {
  auto r = Parse("program prg(input logic clk); endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports.size(), 1u);
}

// Program with non-ANSI ports.
TEST(SourceText, ProgramNonAnsiHeader) {
  auto r = Parse(
      "program prg(clk);\n"
      "  input clk;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports.size(), 1u);
}

// Program with wildcard ports: program p(.*);
TEST(SourceText, ProgramWildcardPorts) {
  auto r = Parse("program prg(.*); endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->has_wildcard_ports);
}

}  // namespace
