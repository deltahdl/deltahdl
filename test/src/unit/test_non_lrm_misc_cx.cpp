// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

// 11. Multiple packages imported into same module
TEST(ParserClause03, Cl3_13_MultiplePackageImports) {
  auto r = Parse(
      "package alpha;\n"
      "  typedef int alpha_t;\n"
      "endpackage\n"
      "package beta;\n"
      "  typedef int beta_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import alpha::*;\n"
      "  import beta::beta_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 2u);
  auto* mod = r.cu->modules[0];
  int import_count = 0;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kImportDecl) import_count++;
  }
  EXPECT_EQ(import_count, 2);
}

// 20. Package scope resolution (pkg::item)
TEST(ParserClause03, Cl3_13_PackageScopeResolution) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  parameter int WIDTH = 8;\n"
              "endpackage\n"
              "module m;\n"
              "  logic [pkg::WIDTH-1:0] data;\n"
              "endmodule\n"));
}

TEST(ParserA213, PackageImportItemStar) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::*; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->import_item.package_name, "pkg");
  EXPECT_TRUE(item->import_item.is_wildcard);
}

// data_declaration alternative: package_import_declaration
TEST(ParserA28, ImportInBlock) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  int x = 5;\n"
              "endpackage\n"
              "module m;\n"
              "  initial begin\n"
              "    import pkg::*;\n"
              "  end\n"
              "endmodule\n"));
}

// import in task body
TEST(ParserA28, ImportInTask) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  int val = 1;\n"
              "endpackage\n"
              "module m;\n"
              "  task my_task();\n"
              "    import pkg::*;\n"
              "  endtask\n"
              "endmodule\n"));
}

// Multiple imports in one statement in block
TEST(ParserA28, ImportMultipleInBlock) {
  EXPECT_TRUE(
      ParseOk("package p1; int a; endpackage\n"
              "package p2; int b; endpackage\n"
              "module m;\n"
              "  initial begin\n"
              "    import p1::a, p2::b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(Parser, ImportSpecific) {
  auto r = Parse(
      "module t;\n"
      "  import my_pkg::WIDTH;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "my_pkg");
  EXPECT_EQ(item->import_item.item_name, "WIDTH");
  EXPECT_FALSE(item->import_item.is_wildcard);
}

TEST(Parser, ImportWildcard) {
  auto r = Parse(
      "module t;\n"
      "  import my_pkg::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "my_pkg");
  EXPECT_TRUE(item->import_item.is_wildcard);
}

// =============================================================================
// §24.13 Program with import
// =============================================================================
TEST_F(ProgramTestParse, ProgramWithImport) {
  auto* unit = Parse(
      "program p;\n"
      "  import pkg::*;\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kImportDecl);
  EXPECT_TRUE(unit->programs[0]->items[0]->import_item.is_wildcard);
}

// package_item: package_export_declaration — export pkg::item
TEST(SourceText, PackageExportNamed) {
  auto r = Parse(
      "package pkg;\n"
      "  export other_pkg::my_func;\n"
      "  export another::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->packages[0]->items.size(), 2u);
}

TEST(ParserA213, PackageExportSingleItem) {
  auto r = Parse(
      "package pkg;\n"
      "  export other_pkg::some_func;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->packages[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(item->import_item.package_name, "other_pkg");
  EXPECT_EQ(item->import_item.item_name, "some_func");
}

// --- Single-item generate-for without begin/end (§27.4) ---
TEST(ParserSection27, GenerateForSingleItem) {
  auto r = Parse(
      "module m;\n"
      "  for (i = 0; i < 4; i = i + 1)\n"
      "    assign out[i] = in[i];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
}

// --- Single-item generate-if without begin/end (§27.5) ---
TEST(ParserSection27, GenerateIfSingleItemParse) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1)\n"
      "    assign out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_EQ(gen->gen_body.size(), 1);
}

TEST(ParserSection27, GenerateIfSingleItemBody) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1)\n"
      "    assign out = in;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
  EXPECT_EQ(gen->gen_else, nullptr);
}

TEST(ParserSection27, GenerateIfElseSingleItemParse) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1)\n"
      "    assign out = a;\n"
      "  else\n"
      "    assign out = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_EQ(gen->gen_body.size(), 1);
}

TEST(ParserSection27, GenerateIfElseSingleItemBranches) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1)\n"
      "    assign out = a;\n"
      "  else\n"
      "    assign out = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
  ASSERT_NE(gen->gen_else, nullptr);
  ASSERT_EQ(gen->gen_else->gen_body.size(), 1);
  EXPECT_EQ(gen->gen_else->gen_body[0]->kind, ModuleItemKind::kContAssign);
}

// --- Inline genvar in generate-for init (§27.4) ---
TEST(ParserSection27, InlineGenvarInForInitParse) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i = i + 1) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_init, nullptr);
}

TEST(ParserSection27, InlineGenvarInForInitBody) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i = i + 1) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_body.size(), 1);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kContAssign);
}

// --- Generate-for with i++ step (§27.4) ---
TEST(ParserSection27, GenerateForPostIncrement) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_step, nullptr);
  ASSERT_EQ(gen->gen_body.size(), 1);
}

// --- Generate-case (§27.6) ---
TEST(ParserSection27, GenerateCaseParse) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    1: assign out = in;\n"
      "    2: assign out = in2;\n"
      "    default: assign out = 0;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(gen->gen_case_items.size(), 3u);
}

TEST(ParserSection27, GenerateCaseItemDefaults) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    1: assign out = in;\n"
      "    2: assign out = in2;\n"
      "    default: assign out = 0;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  const bool kExpectedDefaults[] = {false, false, true};
  for (size_t i = 0; i < 3; i++) {
    EXPECT_EQ(gen->gen_case_items[i].is_default, kExpectedDefaults[i]);
  }
}

// --- Generate-for with labeled begin/end (§27.4) ---
TEST(ParserSection27, GenerateForLabeled) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : gen_blk\n"
      "    assign out[i] = in[i];\n"
      "  end : gen_blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
}

// --- Generate-if with begin/end blocks (§27.5) ---
TEST(ParserSection27, GenerateIfBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 1) begin\n"
      "    assign a = b;\n"
      "    assign c = d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_GE(gen->gen_body.size(), 2u);
}

// --- Generate-if/else-if chain (§27.5) ---
TEST(ParserSection27, GenerateIfElseIfChainParse) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH == 1)\n"
      "    assign out = a;\n"
      "  else if (WIDTH == 2)\n"
      "    assign out = b;\n"
      "  else\n"
      "    assign out = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else, nullptr);
}

TEST(ParserSection27, GenerateIfElseIfChainNesting) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH == 1)\n"
      "    assign out = a;\n"
      "  else if (WIDTH == 2)\n"
      "    assign out = b;\n"
      "  else\n"
      "    assign out = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->gen_else->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else->gen_else, nullptr);
}

// --- generate...endgenerate wrapper (§27.3) ---
TEST(ParserSection27, GenerateRegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 4; i++) begin\n"
      "      assign out[i] = in[i];\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found_gen_for = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found_gen_for = true;
  }
  EXPECT_TRUE(found_gen_for);
}

TEST(ParserSection27, GenerateForCompoundAssign) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i += 1) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_step, nullptr);
  ASSERT_EQ(gen->gen_body.size(), 1);
}

// --- generate...endgenerate with multiple constructs (§27.1/§27.3) ---
TEST(ParserSection27, GenerateOverview) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    if (A) assign x = 1;\n"
      "    if (B) assign y = 2;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  size_t gen_if_count = 0;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) ++gen_if_count;
  }
  EXPECT_EQ(gen_if_count, 2u);
}

TEST(ParserSection27, GenerateRegionWithMultipleKinds) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 2; i++) begin\n"
      "      assign a[i] = b[i];\n"
      "    end\n"
      "    if (WIDTH > 0)\n"
      "      assign c = d;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found_for = false;
  bool found_if = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found_for = true;
    if (item->kind == ModuleItemKind::kGenerateIf) found_if = true;
  }
  EXPECT_TRUE(found_for);
  EXPECT_TRUE(found_if);
}

// --- Loop generate with module instantiation (§27.4) ---
TEST(ParserSection27, GenerateForWithModuleInst) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : blk\n"
      "    sub u(.a(in[i]), .b(out[i]));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

TEST(ParserSection27, GenerateForNestedBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i++) begin : outer\n"
      "    for (genvar j = 0; j < 2; j++) begin : inner\n"
      "      assign out[i][j] = in[i][j];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* outer = r.cu->modules[0]->items[0];
  EXPECT_EQ(outer->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(outer->gen_body.size(), 1u);
  EXPECT_EQ(outer->gen_body[0]->kind, ModuleItemKind::kGenerateFor);
}

TEST(ParserSection27, GenerateForPreDecrement) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 3; i >= 0; i--) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_step, nullptr);
}

}  // namespace
