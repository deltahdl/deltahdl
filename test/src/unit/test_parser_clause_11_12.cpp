#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- let_port_item ---

TEST(LetDeclParsing, LetPortItem_ExplicitType) {
  auto r = Parse(
      "module m;\n"
      "  let f(logic [15:0] val) = val;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "val");
}

TEST(LetDeclParsing, LetPortItem_WithDefault) {
  auto r = Parse(
      "module m;\n"
      "  let f(x = 42) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

TEST(LetDeclParsing, LetPortItem_NoDefault) {
  auto r = Parse(
      "module m;\n"
      "  let f(x) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->func_args[0].default_value, nullptr);
}

TEST(LetDeclParsing, LetPortItem_WithUnpackedDim) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(logic x [3:0]) = x[0];\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetPortItem_TypedWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  let at_least(logic sig, logic rst = 1'b0) = rst || sig;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].default_value, nullptr);
  EXPECT_NE(item->func_args[1].default_value, nullptr);
}

TEST(LetDeclParsing, LetPortItem_IntType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(int a, int b) = a * b;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetPortItem_BitType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(bit [7:0] x) = x;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetPortItem_RegType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(reg [3:0] r) = r;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetPortItem_AttributeInstance) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* my_attr *) logic x) = x;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetPortItem_AttributeInstanceMultiple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* a = 1 *) x, (* b *) y) = x + y;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetPortItem_ImplicitType) {
  auto r = Parse(
      "module m;\n"
      "  let f(x) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
}

// --- let_formal_type ---

TEST(LetDeclParsing, LetFormalType_Logic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(logic x) = x;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetFormalType_LogicPacked) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(logic [31:0] x) = x;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetFormalType_Integer) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(integer x) = x;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetFormalType_Real) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(real x) = x;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetFormalType_SignedImplicit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(signed [7:0] x) = x;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetFormalType_UnsignedImplicit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(unsigned [7:0] x) = x;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetFormalType_MixedUntypedAndTyped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(untyped a, logic [7:0] b) = b;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetFormalType_Untyped) {
  auto r = Parse(
      "module m;\n"
      "  let f(untyped a) = a;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "a");
}

// --- let_declaration ---

TEST(LetDeclParsing, LetDecl_NoArgs) {
  auto r = Parse(
      "module m;\n"
      "  let addr = base + offset;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "addr");
}

TEST(LetDeclParsing, LetDecl_EmptyParens) {
  auto r = Parse(
      "module m;\n"
      "  let my_val() = 42;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "my_val");
  EXPECT_TRUE(item->func_args.empty());
}

TEST(LetDeclParsing, LetDecl_WithArgs) {
  auto r = Parse(
      "module m;\n"
      "  let op(x, y, z) = |((x | y) & z);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "op");
  ASSERT_EQ(item->func_args.size(), 3u);
}

TEST(LetDeclParsing, LetDecl_HasBodyExpr) {
  auto r = Parse(
      "module m;\n"
      "  let sum(a, b) = a + b;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(LetDeclParsing, LetDecl_ComplexExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let max(a, b) = (a > b) ? a : b;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetDecl_InPackage) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  let my_op(x, y) = x & y;\n"
              "endpackage\n"));
}

TEST(LetDeclParsing, LetDecl_InInterface) {
  EXPECT_TRUE(
      ParseOk("interface ifc;\n"
              "  let bus_ok(req, ack) = req & ack;\n"
              "endinterface\n"));
}

TEST(LetDeclParsing, LetDecl_InProgram) {
  EXPECT_TRUE(
      ParseOk("program p;\n"
              "  let tval(x) = x + 1;\n"
              "endprogram\n"));
}

TEST(LetDeclParsing, LetDecl_InChecker) {
  EXPECT_TRUE(
      ParseOk("checker chk;\n"
              "  let valid(a, b) = a | b;\n"
              "endchecker\n"));
}

TEST(LetDeclParsing, LetDecl_AsBlockItem) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    let local_add(a, b) = a + b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetDecl_Multiple) {
  auto r = Parse(
      "module m;\n"
      "  let add(a, b) = a + b;\n"
      "  let sub(a, b) = a - b;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kLetDecl) count++;
  }
  EXPECT_EQ(count, 2);
}

// --- let_identifier ---

TEST(LetDeclParsing, LetIdentifier_Simple) {
  auto r = Parse(
      "module m;\n"
      "  let foo = 1;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "foo");
}

// --- let_port_list ---

TEST(LetDeclParsing, LetPortList_Single) {
  auto r = Parse(
      "module m;\n"
      "  let f(x) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(LetDeclParsing, LetPortList_Multiple) {
  auto r = Parse(
      "module m;\n"
      "  let f(a, b, c, d) = a + b + c + d;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 4u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[1].name, "b");
  EXPECT_EQ(item->func_args[2].name, "c");
  EXPECT_EQ(item->func_args[3].name, "d");
}

TEST(LetDeclParsing, LetPortList_MixedTypes) {
  auto r = Parse(
      "module m;\n"
      "  let f(logic [7:0] a, int b, c) = a + b + c;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 3u);
}

// --- let_expression ---

TEST(LetDeclParsing, LetExpr_SimpleCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let op(x, y) = x + y;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = op(3, 4);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetExpr_NoArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let val = 42;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = val;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetExpr_EmptyParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let val() = 42;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = val();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetExpr_PackageScope) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  let add(x, y) = x + y;\n"
              "endpackage\n"
              "module m;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = pkg::add(1, 2);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetExpr_InAssign) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let add(a, b) = a + b;\n"
              "  logic [7:0] w;\n"
              "  assign w = add(8'd1, 8'd2);\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetExpr_Nested) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let inc(x) = x + 1;\n"
              "  let dbl(x) = x * 2;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = dbl(inc(3));\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetExpr_InConditional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let valid(x) = x != 0;\n"
              "  initial begin\n"
              "    int a;\n"
              "    if (valid(a)) a = 0;\n"
              "  end\n"
              "endmodule\n"));
}

// --- let_list_of_arguments ---

TEST(LetDeclParsing, LetArgs_SinglePositional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(5);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetArgs_MultiplePositional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(a, b, c) = a + b + c;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(1, 2, 3);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetArgs_Named) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(a, b) = a + b;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(.a(1), .b(2));\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetArgs_DefaultOmitted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(a, b = 10) = a + b;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(5);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetArgs_AllNamed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let arb(request, valid, override) = "
              "    |(request & valid) || override;\n"
              "  initial begin\n"
              "    logic result;\n"
              "    result = arb(.request(2'b11), .valid(2'b10),"
              " .override(1'b0));\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetArgs_ExprInArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x, y) = x + y;\n"
              "  initial begin\n"
              "    int a, b, z;\n"
              "    z = f(a * 2, b + 1);\n"
              "  end\n"
              "endmodule\n"));
}

// --- let_actual_arg ---

TEST(LetDeclParsing, LetActualArg_Literal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(42);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetActualArg_Variable) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int a, z;\n"
              "    z = f(a);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetActualArg_BinaryExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int a, b, z;\n"
              "    z = f(a + b);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetActualArg_Ternary) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int a, z;\n"
              "    z = f(a > 0 ? a : -a);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetActualArg_Concatenation) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    logic [7:0] z;\n"
              "    z = f({4'b0, 4'b1});\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetActualArg_FunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int inc(int x); return x + 1; endfunction\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(inc(5));\n"
              "  end\n"
              "endmodule\n"));
}

// --- LetDeclParsing (declaration variants) ---

TEST(LetDeclParsing, DeclNoArgsBody) {
  auto r = Parse(
      "module t;\n"
      "  let addr = top.block1.base + top.block1.displ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_TRUE(let_item->func_args.empty());
  ASSERT_NE(let_item->init_expr, nullptr);
}

TEST(LetDeclParsing, DeclWithArgsNames) {
  auto r = Parse(
      "module t;\n"
      "  let op(x, y, z) = |((x | y) & z);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  ASSERT_EQ(let_item->func_args.size(), 3u);
  const char* const kExpected[] = {"x", "y", "z"};
  for (size_t i = 0; i < 3; i++) {
    EXPECT_EQ(let_item->func_args[i].name, kExpected[i]);
  }
  ASSERT_NE(let_item->init_expr, nullptr);
}

TEST(LetDeclParsing, DeclWithDefaultsArgs) {
  auto r = Parse(
      "module t;\n"
      "  let at_least_two(sig, rst = 1'b0) = rst || sig;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_EQ(let_item->func_args[0].name, "sig");
  EXPECT_EQ(let_item->func_args[0].default_value, nullptr);
  EXPECT_EQ(let_item->func_args[1].name, "rst");
  EXPECT_NE(let_item->func_args[1].default_value, nullptr);
}

TEST(LetDeclParsing, DeclTypedArgsNames) {
  auto r = Parse(
      "module t;\n"
      "  let mult(logic [15:0] x, logic [15:0] y) = x * y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  ASSERT_EQ(let_item->func_args.size(), 2u);
  EXPECT_EQ(let_item->func_args[0].name, "x");
  EXPECT_EQ(let_item->func_args[1].name, "y");
}

// --- let_declaration in block items ---

TEST(LetDeclParsing, LetDeclInFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void foo();\n"
              "    let inc(x) = x + 1;\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetDeclNoArgsInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    let val = 42;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetDeclInTask) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task();\n"
              "    let inc(x) = x + 1;\n"
              "  endtask\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetDeclInForkJoin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    let val = 99;\n"
              "  join\n"
              "endmodule\n"));
}

// --- let_declaration in clocking block ---

TEST(LetDeclParsing, LetDeclInClockingBlock) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    let valid = data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}

// --- Error conditions and edge cases ---

TEST(LetDeclParsing, ErrorMissingEquals) {
  auto r = Parse(
      "module m;\n"
      "  let f(x) x;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LetDeclParsing, ErrorMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  let f(x) = x\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LetDeclParsing, ErrorMissingIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  let = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LetDeclParsing, ErrorMissingBody) {
  auto r = Parse(
      "module m;\n"
      "  let f(x) = ;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LetDeclParsing, ErrorUnclosedParens) {
  auto r = Parse(
      "module m;\n"
      "  let f(x = x;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LetDeclParsing, ErrorEmptyBodyNoEquals) {
  auto r = Parse(
      "module m;\n"
      "  let f;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(LetDeclParsing, LetDeclInGenerateBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  generate\n"
              "    if (1) begin\n"
              "      let g(x) = x + 1;\n"
              "    end\n"
              "  endgenerate\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetDeclWithManyArgs) {
  auto r = Parse(
      "module m;\n"
      "  let wide(a, b, c, d, e, f, g, h) = a+b+c+d+e+f+g+h;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 8u);
}

TEST(LetDeclParsing, LetDeclMixedDefaultAndNonDefault) {
  auto r = Parse(
      "module m;\n"
      "  let f(a, b = 1, c = 2) = a + b + c;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].default_value, nullptr);
  EXPECT_NE(item->func_args[1].default_value, nullptr);
  EXPECT_NE(item->func_args[2].default_value, nullptr);
}

TEST(LetDeclParsing, LetDeclAllUntyped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(untyped a, untyped b, untyped c) = a + b + c;\n"
              "endmodule\n"));
}

TEST(LetDeclParsing, LetCallInAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let inc(x) = x + 1;\n"
              "  always @(*) begin\n"
              "    int y;\n"
              "    y = inc(3);\n"
              "  end\n"
              "endmodule\n"));
}

// --- let as subexpression shortcut (§11.12 Example) ---

TEST(LetDeclParsing, LetAsSubexpressionShortcut) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let addr = top.block1.unit1.base + top.block1.unit2.displ;\n"
              "  initial begin\n"
              "    logic [31:0] val;\n"
              "    val = addr;\n"
              "  end\n"
              "endmodule\n"));
}

// --- package-scoped let with import ---

TEST(LetDeclParsing, LetDeclImportedFromPackage) {
  EXPECT_TRUE(
      ParseOk("package pex;\n"
              "  let valid_arb(request, valid, override) = "
              "    |(request & valid) || override;\n"
              "endpackage\n"
              "module m;\n"
              "  import pex::*;\n"
              "  logic [1:0] req, vld;\n"
              "  logic ovr, result;\n"
              "  initial begin\n"
              "    result = valid_arb(.request(req), .valid(vld), "
              ".override(ovr));\n"
              "  end\n"
              "endmodule\n"));
}

// --- let in compilation-unit scope ---

TEST(LetDeclParsing, LetDeclInCompilationUnitScope) {
  EXPECT_TRUE(
      ParseOk("let global_add(a, b) = a + b;\n"
              "module m;\n"
              "endmodule\n"));
}

// --- let with body using $bits ---

TEST(LetDeclParsing, LetBodyWithSystemFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let mult(x, y) = ($bits(x) + $bits(y))'(x * y);\n"
              "endmodule\n"));
}

// --- mixed positional and named arguments ---

TEST(LetDeclParsing, LetArgsMixedPositionalAndNamed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(a, b, c) = a + b + c;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(1, .b(2), .c(3));\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
