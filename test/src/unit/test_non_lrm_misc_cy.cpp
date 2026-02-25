// Non-LRM tests

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
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

namespace {

// =============================================================================
// LRM section 27.1 -- General (generate constructs overview)
// =============================================================================
// §27.1: Generate-for with module instantiation (structural repetition).
TEST(ParserSection27, GenerateForWithModuleInst2) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : gen_inst\n"
      "    sub u(.a(w[i]));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  auto* gen = mod->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

// §27.1: Generate-if with nested generate-for (hierarchical conditional).
TEST(ParserSection27, GenerateIfWithNestedFor) {
  auto r = Parse(
      "module m;\n"
      "  if (USE_PIPELINE) begin\n"
      "    for (genvar i = 0; i < STAGES; i++) begin : stage\n"
      "      assign pipe[i] = data[i];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  ASSERT_GE(mod->items[0]->gen_body.size(), 1u);
  EXPECT_EQ(mod->items[0]->gen_body[0]->kind, ModuleItemKind::kGenerateFor);
}

// §27.1: Multiple generate constructs in sequence.
TEST(ParserSection27, MultipleGenerateConstructs) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : g1\n"
      "    assign a[i] = b[i];\n"
      "  end\n"
      "  if (MODE) begin\n"
      "    assign x = y;\n"
      "  end\n"
      "  case (SEL)\n"
      "    0: assign out = a;\n"
      "    default: assign out = b;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 3u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateFor);
  EXPECT_EQ(mod->items[1]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_EQ(mod->items[2]->kind, ModuleItemKind::kGenerateCase);
}

// §27.1: Generate-for with always block body.
TEST(ParserSection27, GenerateForWithAlwaysBlock) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : gen_alw\n"
      "    always @(posedge clk)\n"
      "      q[i] <= d[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kAlwaysBlock);
}

TEST(Parser, GenerateFor) {
  auto r = Parse(
      "module t;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin\n"
      "    assign a[i] = b[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* gen =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen, nullptr);
  EXPECT_NE(gen->gen_init, nullptr);
  EXPECT_NE(gen->gen_cond, nullptr);
  EXPECT_NE(gen->gen_step, nullptr);
  EXPECT_FALSE(gen->gen_body.empty());
}

// §3.3 Generate blocks
TEST(ParserClause03, Cl3_3_GenerateBlocks) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter N = 4) ();\n"
              "  genvar i;\n"
              "  generate\n"
              "    for (i = 0; i < N; i = i + 1) begin : gen_loop\n"
              "      logic [7:0] data;\n"
              "    end\n"
              "  endgenerate\n"
              "endmodule\n"));
}

// 14. Generate block scope (for-generate)
TEST(ParserClause03, Cl3_13_GenerateForBlockScope) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen_blk\n"
      "    logic [7:0] data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_gen = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) {
      found_gen = true;
      EXPECT_FALSE(item->gen_body.empty());
    }
  }
  EXPECT_TRUE(found_gen);
}

// --- genvar_declaration ---
// genvar list_of_genvar_identifiers ;
TEST(ParserA213, GenvarDeclSingle) {
  auto r = Parse("module m; genvar i; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "i");
}

TEST(ParserA213, GenvarDeclMultiple) {
  auto r = Parse("module m; genvar i, j, k; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
}

// --- list_of_genvar_identifiers ---
// genvar_identifier { , genvar_identifier }
TEST(ParserA23, ListOfGenvarIdentifiersSingle) {
  auto r = Parse("module m; genvar i; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "i");
}

static void VerifyGenerateCaseItem(const GenerateCaseItem& ci, size_t idx,
                                   bool expect_default,
                                   size_t expect_pattern_count) {
  EXPECT_EQ(ci.is_default, expect_default) << "case item " << idx;
  EXPECT_EQ(ci.patterns.size(), expect_pattern_count) << "case item " << idx;
  EXPECT_FALSE(ci.body.empty()) << "case item " << idx;
}

TEST(Parser, GenerateIf) {
  auto r = Parse(
      "module t;\n"
      "  if (WIDTH > 8) begin\n"
      "    assign a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(mod->items[0]->gen_cond, nullptr);
  EXPECT_FALSE(mod->items[0]->gen_body.empty());
}

TEST(Parser, GenerateIfElse) {
  auto r = Parse(
      "module t;\n"
      "  if (WIDTH > 8) begin\n"
      "    assign a = b;\n"
      "  end else begin\n"
      "    assign a = c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(item->gen_else, nullptr);
}

TEST(Parser, GenerateCase) {
  auto r = Parse(
      "module t;\n"
      "  case (WIDTH)\n"
      "    1: begin\n"
      "      assign a = b;\n"
      "    end\n"
      "    2: begin\n"
      "      assign a = c;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateCase);
  EXPECT_NE(item->gen_cond, nullptr);
  ASSERT_EQ(item->gen_case_items.size(), 2);
  VerifyGenerateCaseItem(item->gen_case_items[0], 0, false, 1);
  VerifyGenerateCaseItem(item->gen_case_items[1], 1, false, 1);
}

TEST(Parser, GenerateCaseDefault) {
  auto r = Parse(
      "module t;\n"
      "  case (WIDTH)\n"
      "    1: begin\n"
      "      assign a = b;\n"
      "    end\n"
      "    default: begin\n"
      "      assign a = c;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->gen_case_items.size(), 2);
  EXPECT_TRUE(item->gen_case_items[1].is_default);
}

TEST(Parser, GenerateCaseMultiPattern) {
  auto r = Parse(
      "module t;\n"
      "  case (WIDTH)\n"
      "    1, 2: begin\n"
      "      assign a = b;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->gen_case_items.size(), 1);
  EXPECT_EQ(item->gen_case_items[0].patterns.size(), 2);
}

TEST(Parser, GenerateCaseInRegion) {
  auto r = Parse(
      "module t;\n"
      "  generate\n"
      "    case (WIDTH)\n"
      "      1: begin\n"
      "        assign a = b;\n"
      "      end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateCase) {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// 15. Labeled generate blocks (if-generate)
TEST(ParserClause03, Cl3_13_LabeledIfGenerateBlock) {
  auto r = Parse(
      "module m;\n"
      "  parameter USE_FAST = 1;\n"
      "  if (USE_FAST) begin : fast_path\n"
      "    logic [7:0] result;\n"
      "  end else begin : slow_path\n"
      "    logic [15:0] result;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_gen_if = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) {
      found_gen_if = true;
      EXPECT_FALSE(item->gen_body.empty());
    }
  }
  EXPECT_TRUE(found_gen_if);
}

struct ParseResult307 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult307 Parse(const std::string& src) {
  ParseResult307 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool HasGateOfKind(const std::vector<ModuleItem*>& items,
                          GateKind kind) {
  for (const auto* item : items)
    if (item->kind == ModuleItemKind::kGateInst && item->gate_kind == kind)
      return true;
  return false;
}

// =============================================================================
// LRM §3.7 — Primitives
// =============================================================================
// §3.7:
//       — logic gates and switches instantiated inside a module.
TEST(ParserClause03, Cl3_7_BuiltInPrimitives) {
  auto r = Parse(
      "module gate_test(input a, b, c, output w, x, y, z);\n"
      "  and g1(w, a, b);\n"
      "  nand g2(x, a, b, c);\n"
      "  bufif0 g3(y, a, b);\n"
      "  nmos g4(z, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kGateInst), 4);
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kAnd));
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kNand));
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kBufif0));
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kNmos));
}

TEST(ParserSection28, BasicAndGate) {
  auto r = Parse(
      "module m;\n"
      "  and g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_EQ(item->gate_inst_name, "g1");
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, BasicOrGate) {
  auto r = Parse(
      "module m;\n"
      "  or (out, a, b, c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kOr);
  EXPECT_TRUE(item->gate_inst_name.empty());
  ASSERT_EQ(item->gate_terminals.size(), 4);
}

TEST(ParserSection28, AllNInputGates) {
  auto r = Parse(
      "module m;\n"
      "  and (o, a, b);\n"
      "  nand (o, a, b);\n"
      "  or (o, a, b);\n"
      "  nor (o, a, b);\n"
      "  xor (o, a, b);\n"
      "  xnor (o, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 6);
  GateKind expected[] = {GateKind::kAnd, GateKind::kNand, GateKind::kOr,
                         GateKind::kNor, GateKind::kXor,  GateKind::kXnor};
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(mod->items[i]->gate_kind, expected[i]);
  }
}

// --- Drive strength in gate instantiation context ---
TEST(ParserA222, DriveStrengthGateInst) {
  // drive_strength used with gate instantiation
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and (supply0, supply1) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // wire y, a, b creates 3 items; gate is at index 3
  auto* item = r.cu->modules[0]->items[3];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->drive_strength0, 5u);  // supply0 = 5
  EXPECT_EQ(item->drive_strength1, 5u);  // supply1 = 5
}

TEST(ParserSection28, BasicBufGate) {
  auto r = Parse(
      "module m;\n"
      "  buf b1(out, in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kBuf);
  EXPECT_EQ(item->gate_inst_name, "b1");
  ASSERT_EQ(item->gate_terminals.size(), 2);
}

TEST(ParserSection28, BasicNotGate) {
  auto r = Parse(
      "module m;\n"
      "  not n1(out, in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kNot);
}

TEST(ParserSection28, GateArrayRange) {
  auto r = Parse(
      "module m;\n"
      "  nand n[0:3](out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kNand);
}

TEST(ParserSection28, GateArrayWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  and #5 g[0:7](out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_NE(item->gate_delay, nullptr);
}

static void VerifyGateInstances(const std::vector<ModuleItem*>& items,
                                GateKind kind,
                                const std::string expected_names[],
                                size_t count) {
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(items[i]->gate_kind, kind);
    EXPECT_EQ(items[i]->gate_inst_name, expected_names[i]);
    EXPECT_EQ(items[i]->gate_terminals.size(), 3);
  }
}

static void VerifyStrengthDelayInstances(const std::vector<ModuleItem*>& items,
                                         size_t count, int str0, int str1) {
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(items[i]->drive_strength0, str0);
    EXPECT_EQ(items[i]->drive_strength1, str1);
    EXPECT_NE(items[i]->gate_delay, nullptr);
  }
}

TEST(ParserSection28, MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  and g1(a, b, c), g2(d, e, f);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  std::string expected_names[] = {"g1", "g2"};
  VerifyGateInstances(mod->items, GateKind::kAnd, expected_names, 2);
}

TEST(ParserSection28, MultipleInstancesThree) {
  auto r = Parse(
      "module m;\n"
      "  nand n1(a, b, c), n2(d, e, f), n3(g, h, i);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 3);
  EXPECT_EQ(mod->items[0]->gate_inst_name, "n1");
  EXPECT_EQ(mod->items[1]->gate_inst_name, "n2");
  EXPECT_EQ(mod->items[2]->gate_inst_name, "n3");
}

TEST(ParserSection28, MultipleInstancesNoNames) {
  auto r = Parse(
      "module m;\n"
      "  or (a, b, c), (d, e, f);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  EXPECT_TRUE(mod->items[0]->gate_inst_name.empty());
  EXPECT_TRUE(mod->items[1]->gate_inst_name.empty());
}

TEST(ParserSection28, MultipleInstancesWithStrengthAndDelay) {
  auto r = Parse(
      "module m;\n"
      "  and (strong0, strong1) #5 g1(a, b, c), g2(d, e, f);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  VerifyStrengthDelayInstances(mod->items, 2, 4, 4);
}

TEST(ParserSection28, StrengthWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  and (strong0, strong1) #5 g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 4);  // strong0
  EXPECT_EQ(item->drive_strength1, 4);  // strong1
  EXPECT_NE(item->gate_delay, nullptr);
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

TEST(Parser, GateNoInstanceName) {
  auto r = Parse("module t; and (out, a, b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_TRUE(item->gate_inst_name.empty());
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

static RtlirDesign* ElaborateSrc(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

TEST(ParserSection28, ElaborateAndGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, a, b;\n"
      "  and g1(out, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  // Gate should produce a continuous assign.
  ASSERT_GE(mod->assigns.size(), 1);
  auto& ca = mod->assigns[0];
  EXPECT_NE(ca.lhs, nullptr);
  EXPECT_NE(ca.rhs, nullptr);
  // The rhs should be a binary '&' expression.
  EXPECT_EQ(ca.rhs->op, TokenKind::kAmp);
}

TEST(ParserSection28, ElaborateOrGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, a, b;\n"
      "  or g1(out, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  EXPECT_EQ(mod->assigns[0].rhs->op, TokenKind::kPipe);
}

TEST(ParserSection28, ElaborateNandGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, a, b;\n"
      "  nand g1(out, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  // nand -> ~(a & b): unary kTilde wrapping binary kAmp.
  auto* rhs = mod->assigns[0].rhs;
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
  EXPECT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmp);
}

TEST(ParserSection28, ElaborateXorGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, a, b;\n"
      "  xor g1(out, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  EXPECT_EQ(mod->assigns[0].rhs->op, TokenKind::kCaret);
}

TEST(ParserSection28, ElaborateBufGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, in;\n"
      "  buf b1(out, in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  // buf: out = in (identity), rhs is an identifier.
  EXPECT_EQ(mod->assigns[0].rhs->kind, ExprKind::kIdentifier);
}

TEST(ParserSection28, ElaborateNotGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, in;\n"
      "  not n1(out, in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  // not: out = ~in, rhs is unary kTilde.
  EXPECT_EQ(mod->assigns[0].rhs->op, TokenKind::kTilde);
}

TEST(ParserSection28, ElaborateMultiInputAnd) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out, a, b, c;\n"
      "  and g1(out, a, b, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  // 3-input and: (a & b) & c -- nested binary.
  auto* rhs = mod->assigns[0].rhs;
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

TEST(ParserSection28, ElaboratePullupGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out;\n"
      "  pullup (out);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  // pullup: out = 1'b1
  EXPECT_EQ(mod->assigns[0].rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(mod->assigns[0].rhs->int_val, 1);
}

// --- Gate primitive tests ---
TEST(Parser, GateAndInst) {
  auto r = Parse("module t; and g1(out, a, b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_EQ(item->gate_inst_name, "g1");
  EXPECT_EQ(item->gate_terminals.size(), 3u);
}

TEST(Parser, GateNandWithDelay) {
  auto r = Parse("module t; nand #(5) g2(out, a, b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kNand);
  EXPECT_EQ(item->gate_inst_name, "g2");
  EXPECT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_terminals.size(), 3u);
}

TEST(ParserSection28, PassGateTran) {
  auto r = Parse(
      "module m;\n"
      "  tran (a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kTran);
  ASSERT_EQ(item->gate_terminals.size(), 2);
}

TEST(ParserSection28, MosSwitchNmos) {
  auto r = Parse(
      "module m;\n"
      "  nmos n1(out, data, control);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kNmos);
  EXPECT_EQ(item->gate_inst_name, "n1");
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, CmosSwitchCmos) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(out, data, ncontrol, pcontrol);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kCmos);
  EXPECT_EQ(item->gate_inst_name, "c1");
  ASSERT_EQ(item->gate_terminals.size(), 4);
}

TEST(ParserSection28, ElaboratePulldownGate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  wire out;\n"
      "  pulldown (out);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1);
  EXPECT_EQ(mod->assigns[0].rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(mod->assigns[0].rhs->int_val, 0);
}

TEST(Parser, GateBufMultiOutput) {
  auto r = Parse("module t; buf (o1, o2, in); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kBuf);
  EXPECT_TRUE(item->gate_inst_name.empty());
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, EnableGates) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "  bufif1 (out, in, en);\n"
      "  notif0 (out, in, en);\n"
      "  notif1 (out, in, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 4);
  GateKind expected[] = {GateKind::kBufif0, GateKind::kBufif1,
                         GateKind::kNotif0, GateKind::kNotif1};
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(mod->items[i]->gate_kind, expected[i]);
  }
}

TEST(Parser, GateBufif0) {
  auto r = Parse("module t; bufif0 b1(out, in, en); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kBufif0);
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, PullGates) {
  auto r = Parse(
      "module m;\n"
      "  pullup (out);\n"
      "  pulldown (out);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->gate_kind, GateKind::kPullup);
  EXPECT_EQ(mod->items[1]->gate_kind, GateKind::kPulldown);
}

TEST(Parser, GateNmos) {
  auto r = Parse("module t; nmos (out, in, ctrl); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kNmos);
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(ParserSection28, GateWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  and #5 g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_NE(item->gate_delay, nullptr);
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

TEST(Parser, GateTran) {
  auto r = Parse("module t; tran (a, b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kTran);
  EXPECT_EQ(item->gate_terminals.size(), 2);
}

TEST(ParserSection28, StrengthSpec) {
  auto r = Parse(
      "module m;\n"
      "  and (strong0, weak1) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_EQ(item->drive_strength0, 4);  // strong0 = 4
  EXPECT_EQ(item->drive_strength1, 2);  // weak1 = 2
  EXPECT_EQ(item->gate_inst_name, "g1");
}

TEST(Parser, GateCmos) {
  auto r = Parse("module t; cmos (out, in, nctrl, pctrl); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kCmos);
  EXPECT_EQ(item->gate_terminals.size(), 4);
}

TEST(ParserSection28, GateWithParenDelay) {
  auto r = Parse(
      "module m;\n"
      "  or #(10) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->gate_delay, nullptr);
}

TEST(ParserSection28, StrengthSpecSupply) {
  auto r = Parse(
      "module m;\n"
      "  nand (supply0, supply1) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 5);  // supply0 = 5
  EXPECT_EQ(item->drive_strength1, 5);  // supply1 = 5
}

TEST(ParserSection28, StrengthSpecHighz) {
  auto r = Parse(
      "module m;\n"
      "  or (highz0, pull1) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 1);  // highz0 = 1
  EXPECT_EQ(item->drive_strength1, 3);  // pull1 = 3
}

TEST(Parser, GatePullup) {
  auto r = Parse("module t; pullup (o); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kPullup);
  EXPECT_EQ(item->gate_terminals.size(), 1);
}

TEST(ParserSection28, GateWithTwoDelays) {
  auto r = Parse(
      "module m;\n"
      "  and #(10, 12) a2(out, in1, in2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_NE(item->gate_delay, nullptr);
}

TEST(ParserSection28, GateWithThreeDelays) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 #(10, 12, 11) b3(out, in, ctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kBufif0);
  EXPECT_NE(item->gate_delay, nullptr);
}

TEST(ParserSection28, GateMinTypMaxDelay) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 #(5:7:9, 8:10:12, 15:18:21) b1(io1, io2, dir);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kBufif0);
  EXPECT_NE(item->gate_delay, nullptr);
}

// delay3: three values on gate (rise, fall, turn-off).
TEST(ParserA223, Delay3GateThreeValues) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  bufif1 #(10, 20, 30) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 10u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 20u);
  ASSERT_NE(item->gate_delay_decay, nullptr);
  EXPECT_EQ(item->gate_delay_decay->int_val, 30u);
}

}  // namespace
