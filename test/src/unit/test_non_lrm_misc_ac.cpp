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

TEST(ParserA211, CoverGroup_PortsWithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg(ref int x, input int threshold);\n"
              "    coverpoint x {\n"
              "      bins below = {[0:threshold]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_EmptyCrossBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {}\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_MultipleOptions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.auto_bin_max = 64;\n"
              "    option.weight = 2;\n"
              "    option.goal = 95;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_InPackage) {
  EXPECT_TRUE(
      ParseOk("package p;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endpackage\n"));
}

TEST(ParserA211, CoverGroup_NegedgeEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(negedge rst_n);\n"
              "    coverpoint state;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_ValueRangesInBins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {[$:50]};\n"
              "      bins b = {[51:100]};\n"
              "      bins c = {[101:$]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_CrossThreeItems) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    a_cp: coverpoint a;\n"
              "    b_cp: coverpoint b;\n"
              "    c_cp: coverpoint c;\n"
              "    cross a_cp, b_cp, c_cp;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_BinsWithCoverPointRef) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = {[0:15]} with (item < 10);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_WildcardIllegalIgnore) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      wildcard bins even = {4'b???0};\n"
              "      wildcard bins odd = {4'b???1};\n"
              "      illegal_bins overflow = {[200:255]};\n"
              "      ignore_bins reset = {0};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_ASTVerification) {
  auto r = Parse(
      "module m;\n"
      "  covergroup my_cg @(posedge clk);\n"
      "    coverpoint addr;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "my_cg");
  EXPECT_EQ(item->kind, ModuleItemKind::kCovergroupDecl);
  EXPECT_TRUE(item->loc.IsValid());
}

TEST(ParserA211, CoverGroup_ExtendsASTVerification) {
  auto r = Parse(
      "module m;\n"
      "  covergroup child_cg extends parent_cg;\n"
      "    coverpoint z;\n"
      "  endgroup : child_cg\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "child_cg");
}

TEST(ParserA211, CoverGroup_SampleFunctionASTVerification) {
  auto r = Parse(
      "module m;\n"
      "  covergroup sampled_cg with function sample(int data);\n"
      "    coverpoint data;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "sampled_cg");
}

// =============================================================================
// A.2.12 Production #1: let_declaration
// let_declaration ::= let let_identifier [ ( [ let_port_list ] ) ] = expression
// ;
// =============================================================================
TEST(ParserA212, LetDecl_NoArgs) {
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

TEST(ParserA212, LetDecl_EmptyParens) {
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

TEST(ParserA212, LetDecl_WithArgs) {
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

TEST(ParserA212, LetDecl_HasBodyExpr) {
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

TEST(ParserA212, LetDecl_ComplexExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let max(a, b) = (a > b) ? a : b;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetDecl_InPackage) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  let my_op(x, y) = x & y;\n"
              "endpackage\n"));
}

TEST(ParserA212, LetDecl_InInterface) {
  EXPECT_TRUE(
      ParseOk("interface ifc;\n"
              "  let bus_ok(req, ack) = req & ack;\n"
              "endinterface\n"));
}

TEST(ParserA212, LetDecl_InProgram) {
  EXPECT_TRUE(
      ParseOk("program p;\n"
              "  let tval(x) = x + 1;\n"
              "endprogram\n"));
}

TEST(ParserA212, LetDecl_InChecker) {
  EXPECT_TRUE(
      ParseOk("checker chk;\n"
              "  let valid(a, b) = a | b;\n"
              "endchecker\n"));
}

TEST(ParserA212, LetDecl_AsBlockItem) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    let local_add(a, b) = a + b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetDecl_Multiple) {
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

// =============================================================================
// A.2.12 Production #2: let_identifier
// let_identifier ::= identifier
// =============================================================================
TEST(ParserA212, LetIdentifier_Simple) {
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

TEST(ParserA212, LetIdentifier_Escaped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let \\my+let = 1;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetIdentifier_Underscore) {
  auto r = Parse(
      "module m;\n"
      "  let _my_let_123 = 0;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_my_let_123");
}

// =============================================================================
// A.2.12 Production #3: let_port_list
// let_port_list ::= let_port_item { , let_port_item }
// =============================================================================
TEST(ParserA212, LetPortList_Single) {
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

TEST(ParserA212, LetPortList_Multiple) {
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

TEST(ParserA212, LetPortList_MixedTypes) {
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

// =============================================================================
// A.2.12 Production #4: let_port_item
// let_port_item ::= {attribute_instance} let_formal_type
//     formal_port_identifier {variable_dimension} [= expression]
// =============================================================================
TEST(ParserA212, LetPortItem_ImplicitType) {
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

TEST(ParserA212, LetPortItem_ExplicitType) {
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

TEST(ParserA212, LetPortItem_WithDefault) {
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

TEST(ParserA212, LetPortItem_NoDefault) {
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

TEST(ParserA212, LetPortItem_WithUnpackedDim) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(logic x [3:0]) = x[0];\n"
              "endmodule\n"));
}

TEST(ParserA212, LetPortItem_TypedWithDefault) {
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

TEST(ParserA212, LetPortItem_IntType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(int a, int b) = a * b;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetPortItem_BitType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(bit [7:0] x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetPortItem_RegType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(reg [3:0] r) = r;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetPortItem_AttributeInstance) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* my_attr *) logic x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetPortItem_AttributeInstanceMultiple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* a = 1 *) x, (* b *) y) = x + y;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetPortItem_AttributeWithValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f((* attr = 5 *) int x) = x;\n"
              "endmodule\n"));
}

// =============================================================================
// A.2.12 Production #5: let_formal_type
// let_formal_type ::= data_type_or_implicit | untyped
// =============================================================================
TEST(ParserA212, LetFormalType_Untyped) {
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

TEST(ParserA212, LetFormalType_Implicit) {
  auto r = Parse(
      "module m;\n"
      "  let f(x) = x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(ParserA212, LetFormalType_Logic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(logic x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetFormalType_LogicPacked) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(logic [31:0] x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetFormalType_Integer) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(integer x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetFormalType_Real) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(real x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetFormalType_SignedImplicit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(signed [7:0] x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetFormalType_UnsignedImplicit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(unsigned [7:0] x) = x;\n"
              "endmodule\n"));
}

TEST(ParserA212, LetFormalType_MixedUntypedAndTyped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(untyped a, logic [7:0] b) = b;\n"
              "endmodule\n"));
}

// =============================================================================
// A.2.12 Production #6: let_expression
// let_expression ::= [package_scope] let_identifier
//     [ ( [ let_list_of_arguments ] ) ]
// =============================================================================
TEST(ParserA212, LetExpr_SimpleCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let op(x, y) = x + y;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = op(3, 4);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetExpr_NoArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let val = 42;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = val;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetExpr_EmptyParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let val() = 42;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = val();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetExpr_PackageScope) {
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

TEST(ParserA212, LetExpr_InAssign) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let add(a, b) = a + b;\n"
              "  logic [7:0] w;\n"
              "  assign w = add(8'd1, 8'd2);\n"
              "endmodule\n"));
}

TEST(ParserA212, LetExpr_Nested) {
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

TEST(ParserA212, LetExpr_InConditional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let valid(x) = x != 0;\n"
              "  initial begin\n"
              "    int a;\n"
              "    if (valid(a)) a = 0;\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// A.2.12 Production #7: let_list_of_arguments
// let_list_of_arguments ::=
//     [let_actual_arg] { , [let_actual_arg] }
//         { , .identifier ( [let_actual_arg] ) }
//   | .identifier ( [let_actual_arg] ) { , .identifier ( [let_actual_arg] ) }
// =============================================================================
TEST(ParserA212, LetArgs_SinglePositional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(5);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetArgs_MultiplePositional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(a, b, c) = a + b + c;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(1, 2, 3);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetArgs_Named) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(a, b) = a + b;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(.a(1), .b(2));\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetArgs_DefaultOmitted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(a, b = 10) = a + b;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(5);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetArgs_AllNamed) {
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

TEST(ParserA212, LetArgs_ExprInArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x, y) = x + y;\n"
              "  initial begin\n"
              "    int a, b, z;\n"
              "    z = f(a * 2, b + 1);\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// A.2.12 Production #8: let_actual_arg
// let_actual_arg ::= expression
// =============================================================================
TEST(ParserA212, LetActualArg_Literal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int z;\n"
              "    z = f(42);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetActualArg_Variable) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int a, z;\n"
              "    z = f(a);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetActualArg_BinaryExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int a, b, z;\n"
              "    z = f(a + b);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetActualArg_Ternary) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    int a, z;\n"
              "    z = f(a > 0 ? a : -a);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetActualArg_Concatenation) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let f(x) = x;\n"
              "  initial begin\n"
              "    logic [7:0] z;\n"
              "    z = f({4'b0, 4'b1});\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA212, LetActualArg_FunctionCall) {
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

// =============================================================================
// A.3 -- Primitive instances (gate_instantiation)
// =============================================================================
TEST(ParserAnnexA, A3GateInstNInput) {
  auto r = Parse(
      "module m;\n"
      "  and g1(y, a, b, c);\n"
      "  nand g2(y2, a, b);\n"
      "  xor g3(y3, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int gate_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGateInst) gate_count++;
  }
  EXPECT_EQ(gate_count, 3);
}

TEST(ParserAnnexA, A3GateInstWithStrengthAndDelay) {
  auto r = Parse("module m; and (strong0, weak1) #5 g(y, a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

static ModuleItem* FindGateByKind(const std::vector<ModuleItem*>& items,
                                  GateKind kind) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kGateInst && item->gate_kind == kind)
      return item;
  }
  return nullptr;
}

static std::vector<ModuleItem*> FindAllGates(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> gates;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kGateInst) gates.push_back(item);
  }
  return gates;
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (cmos_switchtype alternative)
// gate_instantiation ::=
//   cmos_switchtype [delay3] cmos_switch_instance {, cmos_switch_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_CmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  cmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, GateInst_RcmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  rcmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, GateInst_CmosWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  cmos #5 (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
}

TEST(ParserA301, GateInst_CmosWithDelay3) {
  auto r = Parse(
      "module m;\n"
      "  cmos #(2, 3, 4) (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_NE(g->gate_delay_fall, nullptr);
  EXPECT_NE(g->gate_delay_decay, nullptr);
}

TEST(ParserA301, GateInst_CmosMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(o1, i1, n1, p1), c2(o2, i2, n2, p2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->gate_inst_name, "c1");
  EXPECT_EQ(gates[1]->gate_inst_name, "c2");
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (mos_switchtype alternative)
// gate_instantiation ::=
//   mos_switchtype [delay3] mos_switch_instance {, mos_switch_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_NmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  nmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_PmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  pmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_RnmosBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rnmos (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_RpmosBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rpmos (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_MosWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  nmos #10 n1(out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_inst_name, "n1");
}

TEST(ParserA301, GateInst_MosMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pmos p1(o1, i1, c1), p2(o2, i2, c2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (enable_gatetype alternative)
// gate_instantiation ::=
//   enable_gatetype [drive_strength] [delay3] enable_gate_instance
//                   {, enable_gate_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_Bufif0Basic) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_Bufif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif1 (out, in, ctrl);\n"
              "endmodule\n"));
}

}  // namespace
