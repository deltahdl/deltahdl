#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "elaboration/type_eval.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/parser.h"

using namespace delta;

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// --- Port binding tests ---

TEST(Elaboration, PortBinding_ResolvesChild) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u0(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  EXPECT_NE(mod->children[0].resolved, nullptr);
  EXPECT_EQ(mod->children[0].resolved->name, "child");
  EXPECT_EQ(mod->children[0].port_bindings.size(), 2);
}

TEST(Elaboration, PortBinding_Direction) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u0(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2);
  EXPECT_EQ(bindings[0].port_name, "a");
  EXPECT_EQ(bindings[0].direction, Direction::kInput);
  EXPECT_EQ(bindings[1].port_name, "b");
  EXPECT_EQ(bindings[1].direction, Direction::kOutput);
}

TEST(Elaboration, PortBinding_UnknownModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic x;\n"
      "  nonexistent u0(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  EXPECT_EQ(mod->children[0].resolved, nullptr);
}

TEST(Elaboration, PortBinding_PortMismatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x;\n"
      "  child u0(.bogus(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  // Port binding still created, but with warning.
  EXPECT_EQ(mod->children[0].port_bindings.size(), 1);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

// --- Width inference tests ---

TEST(Elaboration, WidthInference_ContAssignWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->assigns.size(), 1);
  EXPECT_EQ(mod->assigns[0].width, 8);
}

TEST(Elaboration, WidthInference_BinaryMax) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.int_val = 10;
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.int_val = 20;
  Expr binop;
  binop.kind = ExprKind::kBinary;
  binop.op = TokenKind::kPlus;
  binop.lhs = &lhs;
  binop.rhs = &rhs;
  EXPECT_EQ(InferExprWidth(&binop, typedefs), 32);
}

TEST(Elaboration, WidthInference_ComparisonOneBit) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.int_val = 10;
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.int_val = 20;
  Expr cmp;
  cmp.kind = ExprKind::kBinary;
  cmp.op = TokenKind::kEqEq;
  cmp.lhs = &lhs;
  cmp.rhs = &rhs;
  EXPECT_EQ(InferExprWidth(&cmp, typedefs), 1);
}

TEST(Elaboration, WidthInference_Concatenation) {
  TypedefMap typedefs;
  Expr a;
  a.kind = ExprKind::kIntegerLiteral;
  a.int_val = 1;
  Expr b;
  b.kind = ExprKind::kIntegerLiteral;
  b.int_val = 2;
  Expr concat;
  concat.kind = ExprKind::kConcatenation;
  concat.elements = {&a, &b};
  EXPECT_EQ(InferExprWidth(&concat, typedefs), 64);  // 32 + 32
}

// --- Defparam tests ---

TEST(Elaboration, Defparam_OverridesDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter WIDTH = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.WIDTH = 16;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  auto* child = mod->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_EQ(child->params.size(), 1);
  EXPECT_EQ(child->params[0].resolved_value, 16);
  EXPECT_TRUE(child->params[0].is_resolved);
}

TEST(Elaboration, Defparam_NotFoundWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter WIDTH = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.BOGUS = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

// --- Generate tests ---

TEST(Elaborator, GenerateForCreatesVars) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 3) ();\n"
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

TEST(Elaborator, GenerateForZeroIterations) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 0) ();\n"
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

TEST(Elaborator, GenerateForWithAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter N = 2) ();\n"
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
  EXPECT_EQ(mod->variables[0].name, "i_0_w");
  EXPECT_EQ(mod->variables[1].name, "i_1_w");
}

// --- Typedef tests ---

TEST(Elaborator, TypedefNamedResolution) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef logic [15:0] word_t;\n"
      "  word_t data;\n"
      "  initial data = 1234;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "data") {
      EXPECT_EQ(v.width, 16u);
      EXPECT_TRUE(v.is_4state);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(Elaborator, TypedefChain) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef byte_t octet_t;\n"
      "  octet_t val;\n"
      "  initial val = 255;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "val") {
      EXPECT_EQ(v.width, 8u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// --- Sensitivity inference ---

TEST(Elaborator, AlwaysCombSensitivityInferred) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  always_comb b = a + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->processes.empty());
  const auto& proc = mod->processes[0];
  EXPECT_EQ(proc.kind, RtlirProcessKind::kAlwaysComb);
  EXPECT_FALSE(proc.sensitivity.empty());

  bool found_a = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "a") found_a = true;
  }
  EXPECT_TRUE(found_a);
}

// --- Array init pattern validation (§5.11) ---

TEST(Elaboration, ArrayInitPattern_FlatIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef struct { int a; int b; } ms_t;\n"
      "  ms_t ms[1:0] = '{0, 0, 1, 1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ArrayInitPattern_NestedOk) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef struct { int a; int b; } ms_t;\n"
      "  ms_t ms[1:0] = '{'{0, 0}, '{1, 1}};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, ArrayInitPattern_SimpleArrayOk) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int arr[1:0] = '{10, 20};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, ArrayInitPattern_SizeMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int arr[1:0] = '{10, 20, 30};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §6.5: Variable constraints ---

TEST(Elaboration, VarRedeclare_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  reg v;\n"
      "  wire v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, VarMultiContAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int v;\n"
      "  assign v = 12;\n"
      "  assign v = 13;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, VarMixedAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  wire clk = 0;\n"
      "  int v;\n"
      "  assign v = 12;\n"
      "  always @(posedge clk) v <= ~v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, VarSingleContAssign_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int v;\n"
      "  assign v = 12;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §6.12: Real type restrictions ---

TEST(Elaboration, RealBitSelect_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  wire b;\n"
      "  assign b = a[2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, RealIndex_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  wire [3:0] b;\n"
      "  wire c;\n"
      "  assign c = b[a];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, RealEdge_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  always @(posedge a)\n"
      "    $display(\"posedge\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, RealAssign_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §6.19: Enum validation ---

TEST(Elaboration, EnumSizedLiteralMismatch_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum logic [2:0] {\n"
      "    Global = 4'h2,\n"
      "    Local = 4'h3\n"
      "  } myenum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumXZin2State_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum bit [1:0] {a=0, b=2'bxx, c=1} val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumUnassignedAfterXZ_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum integer {a=0, b={32{1'bx}}, c} val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §6.19.3: Enum strict type checking ---

TEST(Elaboration, EnumStrictTypeCheck_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §6.19.4: Enum arithmetic without cast ---

TEST(Elaboration, EnumArithNoCast_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = a;\n"
      "    val += 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §6.20.5: Specparam restriction ---

TEST(Elaboration, SpecparamInParam_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  parameter p = delay + 2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}
