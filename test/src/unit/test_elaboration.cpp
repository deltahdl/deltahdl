#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "elaboration/sensitivity.h"
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

static RtlirDesign *ElaborateSrc(const std::string &src, ElabFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// --- Port binding tests ---

TEST(Elaboration, PortBinding_ResolvesChild) {
  ElabFixture f;
  auto *design = ElaborateSrc("module child(input logic a, output logic b);\n"
                              "  assign b = a;\n"
                              "endmodule\n"
                              "module top;\n"
                              "  logic x, y;\n"
                              "  child u0(.a(x), .b(y));\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  EXPECT_NE(mod->children[0].resolved, nullptr);
  EXPECT_EQ(mod->children[0].resolved->name, "child");
  EXPECT_EQ(mod->children[0].port_bindings.size(), 2);
}

TEST(Elaboration, PortBinding_Direction) {
  ElabFixture f;
  auto *design = ElaborateSrc("module child(input logic a, output logic b);\n"
                              "  assign b = a;\n"
                              "endmodule\n"
                              "module top;\n"
                              "  logic x, y;\n"
                              "  child u0(.a(x), .b(y));\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  const auto &bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2);

  struct {
    const char *port_name;
    Direction direction;
  } const kExpected[] = {
      {"a", Direction::kInput},
      {"b", Direction::kOutput},
  };
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(bindings[i].port_name, kExpected[i].port_name);
    EXPECT_EQ(bindings[i].direction, kExpected[i].direction);
  }
}

TEST(Elaboration, PortBinding_UnknownModule) {
  ElabFixture f;
  auto *design = ElaborateSrc("module top;\n"
                              "  logic x;\n"
                              "  nonexistent u0(.a(x));\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  EXPECT_EQ(mod->children[0].resolved, nullptr);
}

TEST(Elaboration, PortBinding_PortMismatch) {
  ElabFixture f;
  auto *design = ElaborateSrc("module child(input logic a);\n"
                              "endmodule\n"
                              "module top;\n"
                              "  logic x;\n"
                              "  child u0(.bogus(x));\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  // Port binding still created, but with warning.
  EXPECT_EQ(mod->children[0].port_bindings.size(), 1);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

// --- Width inference tests ---

TEST(Elaboration, WidthInference_ContAssignWidth) {
  ElabFixture f;
  auto *design = ElaborateSrc("module top;\n"
                              "  logic [7:0] a, b;\n"
                              "  assign a = b;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
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
  EXPECT_EQ(InferExprWidth(&concat, typedefs), 64); // 32 + 32
}

// --- Defparam tests ---

TEST(Elaboration, Defparam_OverridesDefault) {
  ElabFixture f;
  auto *design = ElaborateSrc("module child #(parameter WIDTH = 4)();\n"
                              "endmodule\n"
                              "module top;\n"
                              "  child u0();\n"
                              "  defparam u0.WIDTH = 16;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  auto *child = mod->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_EQ(child->params.size(), 1);
}

TEST(Elaboration, Defparam_OverridesDefault_Value) {
  ElabFixture f;
  auto *design = ElaborateSrc("module child #(parameter WIDTH = 4)();\n"
                              "endmodule\n"
                              "module top;\n"
                              "  child u0();\n"
                              "  defparam u0.WIDTH = 16;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *child = design->top_modules[0]->children[0].resolved;
  EXPECT_EQ(child->params[0].resolved_value, 16);
  EXPECT_TRUE(child->params[0].is_resolved);
}

TEST(Elaboration, Defparam_NotFoundWarns) {
  ElabFixture f;
  auto *design = ElaborateSrc("module child #(parameter WIDTH = 4)();\n"
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
  auto *design = ElaborateSrc("module t #(parameter N = 3) ();\n"
                              "  generate\n"
                              "    for (i = 0; i < N; i = i + 1) begin\n"
                              "      logic [31:0] x;\n"
                              "    end\n"
                              "  endgenerate\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  auto *mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[0].name, "i_0_x");
  EXPECT_EQ(mod->variables[1].name, "i_1_x");
  EXPECT_EQ(mod->variables[2].name, "i_2_x");
}

TEST(Elaborator, GenerateForZeroIterations) {
  ElabFixture f;
  auto *design = ElaborateSrc("module t #(parameter N = 0) ();\n"
                              "  generate\n"
                              "    for (i = 0; i < N; i = i + 1) begin\n"
                              "      logic [31:0] x;\n"
                              "    end\n"
                              "  endgenerate\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  auto *mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 0u);
}

TEST(Elaborator, GenerateForWithAssign) {
  ElabFixture f;
  auto *design = ElaborateSrc("module t #(parameter N = 2) ();\n"
                              "  generate\n"
                              "    for (i = 0; i < N; i = i + 1) begin\n"
                              "      logic [31:0] w;\n"
                              "      assign w = 100;\n"
                              "    end\n"
                              "  endgenerate\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->assigns.size(), 2u);
  EXPECT_EQ(mod->variables[0].name, "i_0_w");
  EXPECT_EQ(mod->variables[1].name, "i_1_w");
}

// --- Typedef tests ---

TEST(Elaborator, TypedefNamedResolution) {
  ElabFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  typedef logic [15:0] word_t;\n"
                              "  word_t data;\n"
                              "  initial data = 1234;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  auto *mod = design->top_modules[0];
  bool found = false;
  for (const auto &v : mod->variables) {
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
  auto *design = ElaborateSrc("module t;\n"
                              "  typedef logic [7:0] byte_t;\n"
                              "  typedef byte_t octet_t;\n"
                              "  octet_t val;\n"
                              "  initial val = 255;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  auto *mod = design->top_modules[0];
  bool found = false;
  for (const auto &v : mod->variables) {
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
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [31:0] a, b;\n"
                              "  always_comb b = a + 1;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  auto *mod = design->top_modules[0];
  ASSERT_FALSE(mod->processes.empty());
  const auto &proc = mod->processes[0];
  EXPECT_EQ(proc.kind, RtlirProcessKind::kAlwaysComb);
  EXPECT_FALSE(proc.sensitivity.empty());

  bool found_a = false;
  for (const auto &ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "a")
      found_a = true;
  }
  EXPECT_TRUE(found_a);
}

// --- Array init pattern validation (§5.11) ---

TEST(Elaboration, ArrayInitPattern_FlatIllegal) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
               "  typedef struct { int a; int b; } ms_t;\n"
               "  ms_t ms[1:0] = '{0, 0, 1, 1};\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ArrayInitPattern_NestedOk) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
               "  typedef struct { int a; int b; } ms_t;\n"
               "  ms_t ms[1:0] = '{'{0, 0}, '{1, 1}};\n"
               "endmodule\n",
               f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, ArrayInitPattern_SimpleArrayOk) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
               "  int arr[1:0] = '{10, 20};\n"
               "endmodule\n",
               f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, ArrayInitPattern_SizeMismatch) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
               "  int arr[1:0] = '{10, 20, 30};\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §6.5: Variable constraints ---

TEST(Elaboration, VarRedeclare_Error) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
               "  reg v;\n"
               "  wire v;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, VarMultiContAssign_Error) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
               "  int v;\n"
               "  assign v = 12;\n"
               "  assign v = 13;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, VarMixedAssign_Error) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
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
  ElaborateSrc("module top();\n"
               "  int v;\n"
               "  assign v = 12;\n"
               "endmodule\n",
               f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §6.12: Real type restrictions ---

TEST(Elaboration, RealBitSelect_Error) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
               "  real a = 0.5;\n"
               "  wire b;\n"
               "  assign b = a[2];\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, RealIndex_Error) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
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
  ElaborateSrc("module top();\n"
               "  real a = 0.5;\n"
               "  always @(posedge a)\n"
               "    $display(\"posedge\");\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, RealAssign_Ok) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
               "  real a = 0.5;\n"
               "endmodule\n",
               f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §6.19: Enum validation ---

TEST(Elaboration, EnumSizedLiteralMismatch_Error) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
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
  ElaborateSrc("module top();\n"
               "  enum bit [1:0] {a=0, b=2'bxx, c=1} val;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumUnassignedAfterXZ_Error) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
               "  enum integer {a=0, b={32{1'bx}}, c} val;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §6.19.3: Enum strict type checking ---

TEST(Elaboration, EnumStrictTypeCheck_Error) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
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
  ElaborateSrc("module top();\n"
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
  ElaborateSrc("module top();\n"
               "  specparam delay = 50;\n"
               "  parameter p = delay + 2;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §6.10: Implicit declarations ---

TEST(Elaboration, ImplicitNetOnAssignLhs) {
  // Undeclared identifier on continuous assign LHS creates implicit wire.
  ElabFixture f;
  auto *design = ElaborateSrc("module top;\n"
                              "  assign w = 1'b1;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto *mod = design->top_modules[0];
  // The implicit net 'w' should appear in nets.
  bool found = false;
  for (const auto &n : mod->nets) {
    if (n.name == "w") {
      found = true;
      EXPECT_EQ(n.width, 1) << "implicit net should be scalar";
    }
  }
  EXPECT_TRUE(found) << "implicit net 'w' not created";
}

TEST(Elaboration, ImplicitNetNone_Error) {
  // `default_nettype none causes undeclared identifier to be an error.
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>", "module top;\n"
                                     "  assign w = 1'b1;\n"
                                     "endmodule\n");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  cu->default_nettype = NetType::kNone;
  Elaborator elab(f.arena, f.diag, cu);
  elab.Elaborate("top");
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ImplicitNetOnInstancePort) {
  // Undeclared identifier in instance port connection creates implicit wire.
  ElabFixture f;
  auto *design = ElaborateSrc("module child(input logic a, output logic b);\n"
                              "  assign b = a;\n"
                              "endmodule\n"
                              "module top;\n"
                              "  child u0(.a(x), .b(y));\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto *mod = design->top_modules[0];
  bool found_x = false;
  bool found_y = false;
  for (const auto &n : mod->nets) {
    if (n.name == "x")
      found_x = true;
    if (n.name == "y")
      found_y = true;
  }
  EXPECT_TRUE(found_x) << "implicit net 'x' not created";
  EXPECT_TRUE(found_y) << "implicit net 'y' not created";
}

// --- §6.20.6: Const constants ---

TEST(Elaboration, ConstVarNoInit_Error) {
  // const variable without initializer is an error.
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  const int x;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ConstVarWithInit_OK) {
  // const variable with initializer is fine.
  ElabFixture f;
  auto *design = ElaborateSrc("module top;\n"
                              "  const int x = 42;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, ConstVarReassign_Error) {
  // Assignment to const variable is an error.
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  const int x = 5;\n"
               "  initial x = 10;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §6.14 Chandle restriction tests ---

TEST(Elaboration, ChandlePort_Error) {
  // §6.14: chandle cannot be used as a port.
  ElabFixture f;
  ElaborateSrc("module top(input chandle ch);\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ChandleContAssign_Error) {
  // §6.14: chandle cannot be used in continuous assignment.
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  chandle a, b;\n"
               "  assign a = b;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ChandleSensitivity_Error) {
  // §6.14: chandle cannot appear in event expression.
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  chandle ch;\n"
               "  always @(ch) begin end\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ChandleVarDecl_OK) {
  // §6.14: chandle variable declaration is legal.
  ElabFixture f;
  auto *design = ElaborateSrc("module top;\n"
                              "  chandle ch;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §6.6.8 Interconnect restriction tests ---

TEST(Elaboration, InterconnectContAssign_Error) {
  // §6.6.8: interconnect nets cannot be used in continuous assignments.
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  interconnect sig;\n"
               "  assign sig = 1;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, InterconnectDecl_OK) {
  // §6.6.8: interconnect declaration is legal.
  ElabFixture f;
  auto *design = ElaborateSrc("module top;\n"
                              "  interconnect bus;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  // Check that bus is created as a net.
  ASSERT_FALSE(design->top_modules.empty());
  auto *mod = design->top_modules[0];
  bool found = false;
  for (const auto &n : mod->nets) {
    if (n.name == "bus")
      found = true;
  }
  EXPECT_TRUE(found);
}

// --- §6.25: Parameterized data types ---

TEST(Elaboration, ParameterizedType_Basic) {
  // §6.25: C#(logic)::my_type resolves to logic (width 1).
  ElabFixture f;
  auto *design = ElaborateSrc("class C #(type T = int);\n"
                              "  typedef T my_type;\n"
                              "endclass\n"
                              "module top;\n"
                              "  C#(logic)::my_type x;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].width, 1);
}

TEST(Elaboration, ParameterizedType_Vector) {
  // §6.25: C#(logic [7:0])::my_type resolves to logic [7:0] (width 8).
  ElabFixture f;
  auto *design = ElaborateSrc("class C #(type T = int);\n"
                              "  typedef T my_type;\n"
                              "endclass\n"
                              "module top;\n"
                              "  C#(logic [7:0])::my_type x;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].width, 8);
}

// --- §10.9.2: Struct assignment pattern validation ---

TEST(Elaboration, StructPattern_InvalidMemberName) {
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
               "'{nonexistent: 8'hFF};\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, StructPattern_DuplicateKey) {
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
               "'{a: 8'h01, a: 8'h02};\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// =============================================================================
// §7.3.1: Packed union validation
// =============================================================================

TEST(Elaboration, HardPackedUnion_SameWidth_OK) {
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
               "endmodule\n",
               f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, HardPackedUnion_DifferentWidth_Error) {
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  union packed { logic [7:0] a; logic [15:0] b; } u;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, SoftPackedUnion_DifferentWidth_OK) {
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  union soft { logic [7:0] a; logic [15:0] b; } u;\n"
               "endmodule\n",
               f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.2.2: Packed struct members shall not have individual default values.
TEST(Elaboration, PackedStructMemberDefault_Rejected) {
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  struct packed { bit [3:0] lo = 5; bit [3:0] hi; } s;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, UnpackedStructMemberDefault_Allowed) {
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  struct { int a = 1; int b = 2; } s;\n"
               "endmodule\n",
               f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.9.8: Assoc array index width propagated to RtlirVariable.
TEST(Elaboration, AssocArrayByteIndexWidth) {
  ElabFixture f;
  auto *design = ElaborateSrc("module top;\n"
                              "  int map[byte];\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto &vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 8u);
}

TEST(Elaboration, AssocArrayIntIndexWidth) {
  ElabFixture f;
  auto *design = ElaborateSrc("module top;\n"
                              "  int map[int];\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto &vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 32u);
}

// ==========================================================================
// §9.2.2.2: Implicit sensitivity from longest static prefix
// ==========================================================================

static Expr *SensId(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Expr *SensSelect(Arena &arena, Expr *base, Expr *index) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = index;
  return e;
}

static Expr *SensIntLit(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

TEST(Sensitivity, SelectConstIdxUsesLSP) {
  // a[1] → LSP is "a[1]", sensitivity should include "a[1]" not "a".
  Arena arena;
  auto *expr = SensSelect(arena, SensId(arena, "a"), SensIntLit(arena, 1));
  std::unordered_set<std::string> reads;
  CollectExprReads(expr, reads);
  EXPECT_TRUE(reads.count("a[1]"));
  EXPECT_FALSE(reads.count("a"));
}

TEST(Sensitivity, SelectVarIdxUsesLSP) {
  // a[i] → LSP is "a", sensitivity includes "a" and "i".
  Arena arena;
  auto *expr = SensSelect(arena, SensId(arena, "a"), SensId(arena, "i"));
  std::unordered_set<std::string> reads;
  CollectExprReads(expr, reads);
  EXPECT_TRUE(reads.count("a"));
  EXPECT_TRUE(reads.count("i"));
}

TEST(Sensitivity, NestedSelectUsesLSP) {
  // a[1][i] → LSP is "a[1]", sensitivity includes "a[1]" and "i".
  Arena arena;
  auto *inner = SensSelect(arena, SensId(arena, "a"), SensIntLit(arena, 1));
  auto *outer = SensSelect(arena, inner, SensId(arena, "i"));
  std::unordered_set<std::string> reads;
  CollectExprReads(outer, reads);
  EXPECT_TRUE(reads.count("a[1]"));
  EXPECT_TRUE(reads.count("i"));
  EXPECT_FALSE(reads.count("a"));
}
