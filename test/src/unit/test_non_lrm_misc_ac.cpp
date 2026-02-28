// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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
