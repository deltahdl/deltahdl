#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class AssignedExpressionsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle Rhs() {
    vpiHandle it = vpi_iterate(vpiContAssign, By("top"));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiRhs, vpi_scan(it));
  }

  static int IntOf(vpiHandle expr) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = -1;
    vpi_get_value(expr, &value);
    return value.value.integer;
  }

  static std::vector<vpiHandle> OperandsOf(vpiHandle op) {
    std::vector<vpiHandle> operands;
    vpiHandle it = vpi_iterate(vpiOperand, op);
    if (it == nullptr) return operands;
    while (vpiHandle operand = vpi_scan(it)) operands.push_back(operand);
    return operands;
  }

  static std::vector<int> ValuesOf(const std::vector<vpiHandle>& exprs) {
    std::vector<int> values;
    values.reserve(exprs.size());
    for (vpiHandle expr : exprs) values.push_back(IntOf(expr));
    return values;
  }

  static std::vector<int> PropertiesOf(int property,
                                       const std::vector<vpiHandle>& exprs) {
    std::vector<int> values;
    values.reserve(exprs.size());
    for (vpiHandle expr : exprs) values.push_back(vpi_get(property, expr));
    return values;
  }

  static std::vector<vpiHandle> ProcedureRightSides() {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    if (kProcs.size() != 1) return {};
    const std::vector<vpiHandle> kAssigns =
        ObjectsOf(vpiStmt, vpi_handle(vpiStmt, kProcs[0]));
    std::vector<vpiHandle> rights;
    rights.reserve(kAssigns.size());
    for (vpiHandle assign : kAssigns) {
      rights.push_back(vpi_handle(vpiRhs, assign));
    }
    return rights;
  }
};

TEST_F(AssignedExpressionsOfARun, APartSelectWithConstantBoundsIsConstant) {
  Run("module top; logic [7:0] r; wire [3:0] w; assign w = r[3:0];\n"
      "endmodule\n");
  vpiHandle select = Rhs();
  ASSERT_NE(select, nullptr);
  ASSERT_EQ(vpi_get(vpiType, select), vpiPartSelect);
  EXPECT_EQ(vpi_get(vpiConstantSelect, select), 1);
}

TEST_F(AssignedExpressionsOfARun, AnIndexedPartSelectWithAVaryingBaseIsNot) {
  Run("module top; logic [7:0] r; logic [2:0] i; wire [3:0] w;\n"
      "  assign w = r[i+:4];\n"
      "endmodule\n");
  vpiHandle select = Rhs();
  ASSERT_NE(select, nullptr);
  ASSERT_EQ(vpi_get(vpiType, select), vpiIndexedPartSelect);
  EXPECT_EQ(vpi_get(vpiConstantSelect, select), 0);
}

TEST(PartSelectConstantSelect, ReadOffTheSelectItsParentAndItsRange) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiObject constant;
  constant.type = vpiConstant;
  VpiObject variable;
  variable.type = vpiIntegerVar;
  VpiObject vector;
  vector.type = vpiLogicVar;
  const auto kSelectOf = [](VpiObject* parent, VpiObject* left,
                            VpiObject* right) {
    VpiObject select;
    select.type = vpiPartSelect;
    select.parent = parent;
    select.left_range = left;
    select.right_range = right;
    return select;
  };
  const auto kConstantSelect = [](VpiObject select) {
    return vpi_get(vpiConstantSelect, VpiHandleOf(&select));
  };
  EXPECT_EQ(kConstantSelect(kSelectOf(&vector, &constant, &constant)), 1);
  EXPECT_EQ(kConstantSelect(kSelectOf(nullptr, &constant, &constant)), 0);

  VpiObject static_array;
  static_array.type = vpiArrayVar;
  static_array.array_type = vpiStaticArray;
  EXPECT_EQ(kConstantSelect(kSelectOf(&static_array, &constant, &constant)), 1);
  VpiObject dynamic_array;
  dynamic_array.type = vpiArrayVar;
  dynamic_array.array_type = vpiDynamicArray;
  EXPECT_EQ(kConstantSelect(kSelectOf(&dynamic_array, &constant, &constant)),
            0);

  VpiObject element;
  element.type = vpiLogicVar;
  element.array_member = true;
  element.parent = &dynamic_array;
  element.index_expr = &constant;
  EXPECT_EQ(kConstantSelect(kSelectOf(&element, &constant, &constant)), 0);

  EXPECT_EQ(kConstantSelect(kSelectOf(&vector, &variable, &constant)), 0);
  EXPECT_EQ(kConstantSelect(kSelectOf(&vector, &constant, &variable)), 0);
  VpiObject indexed;
  indexed.type = vpiIndexedPartSelect;
  indexed.parent = &vector;
  indexed.base_expr = &constant;
  indexed.width_expr = &variable;
  EXPECT_EQ(kConstantSelect(indexed), 0);
  SetGlobalVpiContext(nullptr);
}

TEST_F(AssignedExpressionsOfARun, ACastToAKeywordTypeReachesItsTypespec) {
  Run("module top; logic [7:0] r; wire [31:0] w; assign w = int'(r);\n"
      "endmodule\n");
  vpiHandle cast = Rhs();
  ASSERT_NE(cast, nullptr);
  ASSERT_EQ(vpi_get(vpiOpType, cast), vpiCastOp);
  vpiHandle typespec = vpi_handle(vpiTypespec, cast);
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiIntTypespec);
}

TEST_F(AssignedExpressionsOfARun, ACastToATypedefReachesItsTypespec) {
  Run("module top; typedef logic [3:0] nib_t; logic [7:0] r; wire [3:0] w;\n"
      "  assign w = nib_t'(r);\n"
      "endmodule\n");
  vpiHandle cast = Rhs();
  ASSERT_NE(cast, nullptr);
  ASSERT_EQ(vpi_get(vpiOpType, cast), vpiCastOp);
  vpiHandle typedefs = vpi_iterate(vpiTypedef, By("top"));
  ASSERT_NE(typedefs, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_scan(typedefs)), "nib_t");
  vpi_release_handle(typedefs);
  vpiHandle typespec = vpi_handle(vpiTypespec, cast);
  ASSERT_NE(typespec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "nib_t");
}

vpiHandle CastTypespec(vpiHandle cast) {
  if (cast == nullptr || vpi_get(vpiOpType, cast) != vpiCastOp) return nullptr;
  return vpi_handle(vpiTypespec, cast);
}

std::vector<int> CastTypespecKinds(const std::vector<vpiHandle>& rights) {
  std::vector<int> kinds;
  kinds.reserve(rights.size());
  for (vpiHandle right : rights) {
    vpiHandle typespec = CastTypespec(right);
    kinds.push_back(typespec != nullptr ? vpi_get(vpiType, typespec) : 0);
  }
  return kinds;
}

int FirstRangeSize(vpiHandle typespec) {
  vpiHandle ranges = vpi_iterate(vpiRange, typespec);
  if (ranges == nullptr) return 0;
  const int kSize = vpi_get(vpiSize, vpi_scan(ranges));
  vpi_release_handle(ranges);
  return kSize;
}

TEST_F(AssignedExpressionsOfARun, ASizeCastOfATwoStateOperandIsABitVector) {
  Run("module top; int i; wire [7:0] w; assign w = 8'(i); endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiBitTypespec);
}

TEST_F(AssignedExpressionsOfARun, ASizeCastOfAFourStateOperandIsALogicVector) {
  Run("module top; logic [3:0] r; wire [7:0] w; assign w = 8'(r);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiLogicTypespec);
}

TEST_F(AssignedExpressionsOfARun, ASizeCastOfATwoStateOperationIsABitVector) {
  Run("module top; int i, j; wire [7:0] w; assign w = 8'(i + j);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiBitTypespec);
}

TEST_F(AssignedExpressionsOfARun, ASizeCastOfAMixedOperationIsALogicVector) {
  Run("module top; int i; logic [3:0] r; wire [7:0] w;\n"
      "  assign w = 8'(i + r);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiLogicTypespec);
}

TEST_F(AssignedExpressionsOfARun, ASizeCastKeepsTheNatureOfWhatItCasts) {
  Run("module top; bit [7:0] b; logic [7:0] l; logic [0:3][7:0] r [1:4];\n"
      "  wire [7:0] n [4]; int i; logic a, c; bit [3:0] bt; byte y;\n"
      "  shortint s; longint g; logic [3:0] x;\n"
      "  initial begin\n"
      "    x = 4'(b[i]); x = 4'(b[3:0]); x = 4'(b[i+:4]); x = 4'(l[3:0]);\n"
      "    x = 4'(r[i+1][3]); x = 4'(n[i][3:0]); x = 4'(bt); x = 4'(y);\n"
      "    x = 4'(s); x = 4'(g); x = 4'(-(a <-> c));\n"
      "  end\n"
      "endmodule\n");
  const std::vector<int> kKinds = {
      vpiBitTypespec,   vpiBitTypespec,   vpiBitTypespec,  vpiLogicTypespec,
      vpiLogicTypespec, vpiLogicTypespec, vpiBitTypespec,  vpiBitTypespec,
      vpiBitTypespec,   vpiBitTypespec,   vpiLogicTypespec};
  EXPECT_EQ(CastTypespecKinds(ProcedureRightSides()), kKinds);
}

TEST_F(AssignedExpressionsOfARun, ASizeCastIsAsWideAsItsSizeExpression) {
  Run("module top; localparam W = 6; logic [3:0] r; wire [7:0] w;\n"
      "  assign w = W'(r);\n"
      "endmodule\n");
  ASSERT_NE(CastTypespec(Rhs()), nullptr);
  EXPECT_EQ(vpi_get(vpiSize, Rhs()), 6);
}

TEST_F(AssignedExpressionsOfARun, ASigningCastIsTheOperandsTypeSigned) {
  Run("module top; logic [7:0] r; wire [7:0] w; assign w = signed'(r);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiLogicTypespec);
  EXPECT_EQ(vpi_get(vpiSigned, typespec), 1);
}

TEST_F(AssignedExpressionsOfARun, AnUnsigningCastIsTheOperandsTypeUnsigned) {
  Run("module top; int i; wire [31:0] w; assign w = unsigned'(i);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiIntTypespec);
  EXPECT_EQ(vpi_get(vpiSigned, typespec), 0);
}

TEST_F(AssignedExpressionsOfARun, AConstCastIsTheOperandsType) {
  Run("module top; int i; wire [31:0] w; assign w = const'(i); endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiIntTypespec);
}

TEST_F(AssignedExpressionsOfARun, ACastToATypeParameterHasTheTypeItStandsFor) {
  Run("module sub #(parameter type T = logic [3:0]);\n"
      "  logic [7:0] x; wire [3:0] y; assign y = T'(x);\n"
      "endmodule\n"
      "module top; sub #(.T(bit [3:0])) u(); endmodule\n");
  vpiHandle assigns = vpi_iterate(vpiContAssign, By("top.u"));
  ASSERT_NE(assigns, nullptr);
  vpiHandle typespec = CastTypespec(vpi_handle(vpiRhs, vpi_scan(assigns)));
  vpi_release_handle(assigns);
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiBitTypespec);
}

TEST_F(AssignedExpressionsOfARun, ACastToATypeReferenceHasTheTypeItRefersTo) {
  Run("module top; typedef logic [5:0] six_t; bit [3:0] n; byte s;\n"
      "  logic [15:0] v; int d;\n"
      "  initial begin\n"
      "    d = type(n)'(v); d = type(s)'(v); d = type(six_t)'(v);\n"
      "    d = type(bit [11:0])'(v); d = type(n + n)'(v);\n"
      "  end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kRights = ProcedureRightSides();
  const std::vector<int> kKinds = {vpiBitTypespec, vpiByteTypespec,
                                   vpiLogicTypespec, vpiBitTypespec,
                                   vpiBitTypespec};
  EXPECT_EQ(CastTypespecKinds(kRights), kKinds);
  ASSERT_EQ(kRights.size(), kKinds.size());
  EXPECT_EQ(FirstRangeSize(CastTypespec(kRights[0])), 4);
  EXPECT_STREQ(vpi_get_str(vpiName, CastTypespec(kRights[2])), "six_t");
  EXPECT_EQ(FirstRangeSize(CastTypespec(kRights[3])), 12);
}

TEST_F(AssignedExpressionsOfARun, ACastFindsATypedefOfAPackageOrTheUnit) {
  Run("package pk; typedef logic [3:0] nib_t; typedef bit [5:0] six_t;\n"
      "endpackage\n"
      "package pq; typedef byte one_t; endpackage\n"
      "typedef shortint unit_t;\n"
      "module top; import pk::*; import pq::one_t;\n"
      "  logic [7:0] x; logic [3:0] y;\n"
      "  initial begin\n"
      "    y = pk::nib_t'(x); y = six_t'(x); y = one_t'(x); y = unit_t'(x);\n"
      "  end\n"
      "endmodule\n");
  const std::vector<int> kKinds = {vpiLogicTypespec, vpiBitTypespec,
                                   vpiByteTypespec, vpiShortIntTypespec};
  EXPECT_EQ(CastTypespecKinds(ProcedureRightSides()), kKinds);
}

TEST_F(AssignedExpressionsOfARun,
       ACastInAnInitializerFindsItsTypeInTheInstance) {
  Run("module sub; typedef bit [3:0] nib_t; logic [7:0] r;\n"
      "  logic [3:0] v = nib_t'(r);\n"
      "endmodule\n"
      "module top; logic [7:0] r; byte b = byte'(r); sub u(); endmodule\n");
  vpiHandle keyword = CastTypespec(vpi_handle(vpiExpr, By("top.b")));
  ASSERT_NE(keyword, nullptr);
  EXPECT_EQ(vpi_get(vpiType, keyword), vpiByteTypespec);
  vpiHandle named = CastTypespec(vpi_handle(vpiExpr, By("top.u.v")));
  ASSERT_NE(named, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, named), "nib_t");
}

TEST_F(AssignedExpressionsOfARun,
       ACastInAnInitializerFindsATypedefOfAPackageOrTheUnit) {
  Run("package pk; typedef logic [3:0] nib_t; typedef bit [5:0] six_t;\n"
      "endpackage\n"
      "typedef shortint unit_t;\n"
      "module sub; import pk::*; logic [7:0] x;\n"
      "  logic [3:0] a = pk::nib_t'(x); logic [5:0] b = six_t'(x);\n"
      "  shortint c = unit_t'(x);\n"
      "endmodule\n"
      "module top; sub u(); endmodule\n");
  const std::vector<int> kKinds = {vpiLogicTypespec, vpiBitTypespec,
                                   vpiShortIntTypespec};
  EXPECT_EQ(CastTypespecKinds({vpi_handle(vpiExpr, By("top.u.a")),
                               vpi_handle(vpiExpr, By("top.u.b")),
                               vpi_handle(vpiExpr, By("top.u.c"))}),
            kKinds);
}

TEST_F(AssignedExpressionsOfARun,
       ACastInTheFirstTopsInitializerFindsItsTypedef) {
  Run("module top; typedef bit [3:0] nib_t; logic [7:0] r;\n"
      "  logic [3:0] v = nib_t'(r);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(vpi_handle(vpiExpr, By("top.v")));
  ASSERT_NE(typespec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "nib_t");
}

TEST_F(AssignedExpressionsOfARun, ASizeCastIsAsWideAsItsConstantWidth) {
  Run("package pk; parameter W = 2; endpackage\n"
      "module top; localparam W = 3; logic [4:0] b; logic [7:0] x;\n"
      "  logic [5:0] y;\n"
      "  initial begin y = (W+1)'(x); y = ($bits(b))'(x); y = pk::W'(x); end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kRights = ProcedureRightSides();
  EXPECT_EQ(
      CastTypespecKinds(kRights),
      (std::vector<int>{vpiLogicTypespec, vpiLogicTypespec, vpiLogicTypespec}));
  EXPECT_EQ(PropertiesOf(vpiSize, kRights), (std::vector<int>{4, 5, 2}));
}

TEST_F(AssignedExpressionsOfARun, ACastOfAnOperandWithNoObjectHasATypespec) {
  Run("module top; logic a, b; logic [3:0] y;\n"
      "  initial begin\n"
      "    y = 4'(a <-> b); y = signed'(a <-> b); y = const'(a <-> b);\n"
      "  end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kRights = ProcedureRightSides();
  EXPECT_EQ(
      CastTypespecKinds(kRights),
      (std::vector<int>{vpiLogicTypespec, vpiLogicTypespec, vpiLogicTypespec}));
  EXPECT_EQ(PropertiesOf(vpiSize, kRights), (std::vector<int>{4, 1, 1}));
  std::vector<int> signedness;
  for (vpiHandle right : kRights) {
    vpiHandle typespec = CastTypespec(right);
    signedness.push_back(typespec != nullptr ? vpi_get(vpiSigned, typespec)
                                             : -1);
  }
  EXPECT_EQ(signedness, (std::vector<int>{0, 1, 0}));
}

TEST_F(AssignedExpressionsOfARun, ASizeCastOfAnArrayElementIsAsItsElementType) {
  Run("module top; bit [7:0] r [1:4]; bit [7:0] q [$]; bit [7:0] d [];\n"
      "  bit [7:0] m [int]; logic [7:0] l [4]; int i; logic [3:0] x;\n"
      "  initial begin\n"
      "    x = 4'(r[i]); x = 4'(r[i][3]); x = 4'(q[i]); x = 4'(d[i]);\n"
      "    x = 4'(m[i]); x = 4'(l[i]);\n"
      "  end\n"
      "endmodule\n");
  const std::vector<int> kKinds = {vpiBitTypespec, vpiBitTypespec,
                                   vpiBitTypespec, vpiBitTypespec,
                                   vpiBitTypespec, vpiLogicTypespec};
  EXPECT_EQ(CastTypespecKinds(ProcedureRightSides()), kKinds);
}

TEST_F(AssignedExpressionsOfARun, ASizeCastOfAnAggregateIsAsItsMembersAre) {
  Run("module top;\n"
      "  typedef struct packed { bit [3:0] a; byte b; } s2_t;\n"
      "  typedef struct packed { logic [3:0] a; } s4_t;\n"
      "  typedef union packed { bit [3:0] a; bit [3:0] b; } u2_t;\n"
      "  typedef enum { E0, E1 } e_t;\n"
      "  s2_t s; s4_t f; u2_t u; e_t e; s2_t [1:0] p; logic [3:0] x;\n"
      "  initial begin\n"
      "    x = 4'(s); x = 4'(f); x = 4'(u); x = 4'(e); x = 4'(p);\n"
      "  end\n"
      "endmodule\n");
  const std::vector<int> kKinds = {vpiBitTypespec, vpiLogicTypespec,
                                   vpiBitTypespec, vpiBitTypespec,
                                   vpiBitTypespec};
  EXPECT_EQ(CastTypespecKinds(ProcedureRightSides()), kKinds);
}

TEST_F(AssignedExpressionsOfARun,
       ASizeCastOfATasksFourStateStructIsALogicVector) {
  Run("module top; typedef struct packed { logic [3:0] a; } s4_t;\n"
      "  logic [3:0] y;\n"
      "  task t(input s4_t s); y = 4'(s); endtask\n"
      "endmodule\n");
  vpiHandle assign = vpi_handle(vpiStmt, Named(vpiTaskFunc, By("top"), "t"));
  ASSERT_NE(assign, nullptr);
  vpiHandle typespec = CastTypespec(vpi_handle(vpiRhs, assign));
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiLogicTypespec);
}

TEST_F(AssignedExpressionsOfARun,
       ASizeCastOfATwoStateStructWithoutItsOwnStorageIsABitVector) {
  Run("module top; typedef struct packed { bit [3:0] a; byte b; } s2_t;\n"
      "  typedef struct packed { s2_t in; logic c; } o_t;\n"
      "  o_t o; logic [3:0] x, y;\n"
      "  task t(input s2_t s); y = 4'(s); endtask\n"
      "  function void f(); s2_t l; y = 4'(l); endfunction\n"
      "  initial begin x = 4'(o.in); end\n"
      "endmodule\n");
  std::vector<vpiHandle> rights;
  for (const char* name : {"t", "f"}) {
    vpiHandle assign = vpi_handle(vpiStmt, Named(vpiTaskFunc, By("top"), name));
    rights.push_back(assign != nullptr ? vpi_handle(vpiRhs, assign) : nullptr);
  }
  const std::vector<vpiHandle> kProcedure = ProcedureRightSides();
  rights.insert(rights.end(), kProcedure.begin(), kProcedure.end());
  EXPECT_EQ(CastTypespecKinds(rights),
            (std::vector<int>{vpiBitTypespec, vpiBitTypespec, vpiBitTypespec}));
}

TEST_F(AssignedExpressionsOfARun, AnOperationIsSizedByItsSelfDeterminedWidth) {
  Run("module top; wire [7:0] a; wire [5:0] b; wire [7:0] y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(Rhs(), nullptr);
  EXPECT_EQ(vpi_get(vpiSize, Rhs()), 8);
}

TEST_F(AssignedExpressionsOfARun, AnEqualityIsOneBit) {
  Run("module top; wire [7:0] a, b; wire y; assign y = a == b; endmodule\n");
  ASSERT_NE(Rhs(), nullptr);
  EXPECT_EQ(vpi_get(vpiSize, Rhs()), 1);
}

TEST_F(AssignedExpressionsOfARun, ACastIsAsWideAsTheKeywordTypeItNames) {
  Run("module top; logic [3:0] a; logic [63:0] x;\n"
      "  initial begin\n"
      "    x = byte'(a); x = shortint'(a); x = integer'(a); x = longint'(a);\n"
      "    x = time'(a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(PropertiesOf(vpiSize, ProcedureRightSides()),
            (std::vector<int>{8, 16, 32, 64, 64}));
}

TEST_F(AssignedExpressionsOfARun, AConditionalMissingAnOperandIsLeftUnsized) {
  Run("module top; logic a, b, c; logic [7:0] d, x;\n"
      "  initial begin x = c ? (a <-> b) : d; end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kRights = ProcedureRightSides();
  ASSERT_EQ(kRights.size(), 1U);
  ASSERT_EQ(vpi_get(vpiOpType, kRights[0]), vpiConditionOp);
  EXPECT_EQ(OperandsOf(kRights[0]).size(), 2U);
  EXPECT_EQ(vpi_get(vpiSize, kRights[0]), 0);
}

TEST_F(AssignedExpressionsOfARun, PartSelectsAreSizedByTheirRanges) {
  Run("module top; wire [7:0] a; wire [2:0] y; assign y = a[6:4];\n"
      "endmodule\n");
  ASSERT_NE(Rhs(), nullptr);
  EXPECT_EQ(vpi_get(vpiSize, Rhs()), 3);
}

TEST_F(AssignedExpressionsOfARun, AnIndexedPartSelectIsSizedByItsWidth) {
  Run("module top; logic [7:0] r; logic [2:0] i; wire [4:0] w;\n"
      "  assign w = r[i+:5];\n"
      "endmodule\n");
  ASSERT_NE(Rhs(), nullptr);
  EXPECT_EQ(vpi_get(vpiSize, Rhs()), 5);
}

TEST_F(AssignedExpressionsOfARun,
       ConstantExpressionsSizeSelectsAndReplications) {
  Run("module top; localparam W = 4, P = 2, N = 3;\n"
      "  logic [7:0] a, x; logic [1:0] b; logic [2:0] i;\n"
      "  initial begin\n"
      "    x = a[W-1:0]; x = a[4:P]; x = a[i+:W+1]; x = {N{b}};\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(PropertiesOf(vpiSize, ProcedureRightSides()),
            (std::vector<int>{4, 3, 5, 6}));
}

TEST_F(AssignedExpressionsOfARun, ConstantsTheRunValuesSizeTheirExpressions) {
  Run("module top; function automatic int f(); return 3; endfunction\n"
      "  logic [3:0] b; logic [1:0] c; logic [7:0] a, x;\n"
      "  initial begin x = {$bits(b){c}}; x = a[f():0]; end\n"
      "endmodule\n");
  EXPECT_EQ(PropertiesOf(vpiSize, ProcedureRightSides()),
            (std::vector<int>{8, 4}));
}

TEST_F(AssignedExpressionsOfARun, ABitSelectReadsItsBit) {
  Run("module top; integer n = 5; wire y; assign y = n[2]; endmodule\n");
  ASSERT_NE(Rhs(), nullptr);
  ASSERT_EQ(vpi_get(vpiType, Rhs()), vpiBitSelect);
  EXPECT_EQ(IntOf(Rhs()), 1);
}

TEST_F(AssignedExpressionsOfARun, APartSelectReadsItsBits) {
  Run("module top; logic [7:0] r = 8'hA5; wire [3:0] y; assign y = r[7:4];\n"
      "endmodule\n");
  ASSERT_NE(Rhs(), nullptr);
  ASSERT_EQ(vpi_get(vpiType, Rhs()), vpiPartSelect);
  EXPECT_EQ(IntOf(Rhs()), 0xA);
}

TEST_F(AssignedExpressionsOfARun, ANestedKeyedPatternKeepsItsPlace) {
  Run("module top; logic [1:0] a [0:1][0:1];\n"
      "  assign a = '{0: '{1: 2'd1, default: 2'd0}, 1: '{default: 2'd3}};\n"
      "endmodule\n");
  vpiHandle pattern = Rhs();
  ASSERT_NE(pattern, nullptr);
  ASSERT_EQ(vpi_get(vpiOpType, pattern), vpiAssignmentPatternOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(pattern);
  ASSERT_EQ(kOperands.size(), 2U);
  EXPECT_EQ(vpi_get(vpiOpType, kOperands[0]), vpiAssignmentPatternOp);
  EXPECT_EQ(ValuesOf(OperandsOf(kOperands[0])), (std::vector<int>{0, 1}));
  EXPECT_EQ(vpi_get(vpiOpType, kOperands[1]), vpiAssignmentPatternOp);
  EXPECT_EQ(ValuesOf(OperandsOf(kOperands[1])), (std::vector<int>{3, 3}));
}

TEST_F(AssignedExpressionsOfARun, APartSelectThroughAVarSelectHasItsParent) {
  Run("module top; logic [0:3][7:0] r [1:4]; int i, j; wire [1:0] w;\n"
      "  assign w = r[i+1][3][j+:2];\n"
      "endmodule\n");
  vpiHandle select = Rhs();
  ASSERT_NE(select, nullptr);
  ASSERT_EQ(vpi_get(vpiType, select), vpiIndexedPartSelect);
  vpiHandle parent = vpi_handle(vpiParent, select);
  ASSERT_NE(parent, nullptr);
  EXPECT_EQ(vpi_get(vpiType, parent), vpiBitSelect);
  EXPECT_EQ(vpi_get(vpiSize, parent), 8);
  vpiHandle element = vpi_handle(vpiParent, parent);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, element), vpiVarSelect);
}

constexpr const char* kSteppedRightSides =
    "module top; int i, a, b, c, d;\n"
    "  initial begin a = i++; b = ++i; c = i--; d = --i; end\n"
    "endmodule\n";

TEST_F(AssignedExpressionsOfARun, AnIncrementOrDecrementIsAnOperation) {
  Run(kSteppedRightSides);
  const std::vector<vpiHandle> kRights = ProcedureRightSides();
  ASSERT_EQ(kRights.size(), 4U);
  const std::vector<int> kOps = {vpiPostIncOp, vpiPreIncOp, vpiPostDecOp,
                                 vpiPreDecOp};
  for (std::size_t n = 0; n < kRights.size(); ++n) {
    ASSERT_NE(kRights[n], nullptr) << n;
    EXPECT_EQ(vpi_get(vpiType, kRights[n]), vpiOperation) << n;
    EXPECT_EQ(vpi_get(vpiOpType, kRights[n]), kOps[n]) << n;
    const std::vector<vpiHandle> kOperands = OperandsOf(kRights[n]);
    ASSERT_EQ(kOperands.size(), 1U) << n;
    EXPECT_STREQ(vpi_get_str(vpiName, kOperands[0]), "i") << n;
  }
}

TEST_F(AssignedExpressionsOfARun, AnIncrementOrDecrementDecompilesAsWritten) {
  Run(kSteppedRightSides);
  const std::vector<vpiHandle> kRights = ProcedureRightSides();
  ASSERT_EQ(kRights.size(), 4U);
  const std::vector<std::string> kWritten = {"i ++", "++ i", "i --", "-- i"};
  for (std::size_t n = 0; n < kRights.size(); ++n) {
    ASSERT_NE(kRights[n], nullptr) << n;
    const char* decompiled = vpi_get_str(vpiDecompile, kRights[n]);
    ASSERT_NE(decompiled, nullptr) << n;
    EXPECT_EQ(decompiled, kWritten[n]) << n;
  }
}

TEST_F(AssignedExpressionsOfARun, AStepOfASelectDecompilesWithoutParentheses) {
  Run("module top; int r [4]; int i, x;\n"
      "  initial x = -r[i]++;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
  ASSERT_EQ(kProcs.size(), 1U);
  vpiHandle right = vpi_handle(vpiRhs, vpi_handle(vpiStmt, kProcs[0]));
  ASSERT_NE(right, nullptr);
  const char* decompiled = vpi_get_str(vpiDecompile, right);
  ASSERT_NE(decompiled, nullptr);
  EXPECT_STREQ(decompiled, "- r[i] ++");
}

TEST_F(AssignedExpressionsOfARun, EachBinaryOperatorReportsItsOwnOpType) {
  Run("module top; int a, b, x;\n"
      "  initial begin\n"
      "    x = a / b; x = a % b; x = a ** b; x = a ~^ b; x = a ^~ b;\n"
      "    x = a && b; x = a !== b; x = a ==? b; x = a !=? b; x = a >= b;\n"
      "    x = a << b; x = a >> b; x = a <<< b; x = a >>> b;\n"
      "  end\n"
      "endmodule\n");
  const std::vector<int> kOps = {
      vpiDivOp,         vpiModOp,        vpiPowerOp,   vpiBitXnorOp,
      vpiBitXnorOp,     vpiLogAndOp,     vpiCaseNeqOp, vpiWildEqOp,
      vpiWildNeqOp,     vpiGeOp,         vpiLShiftOp,  vpiRShiftOp,
      vpiArithLShiftOp, vpiArithRShiftOp};
  EXPECT_EQ(PropertiesOf(vpiOpType, ProcedureRightSides()), kOps);
}

TEST_F(AssignedExpressionsOfARun, EachUnaryOperatorReportsItsOwnOpType) {
  Run("module top; logic [3:0] a, x;\n"
      "  initial begin\n"
      "    x = +a; x = &a; x = ~&a; x = ~|a; x = ~^a; x = ^~a;\n"
      "  end\n"
      "endmodule\n");
  const std::vector<int> kOps = {vpiPlusOp,     vpiUnaryAndOp,  vpiUnaryNandOp,
                                 vpiUnaryNorOp, vpiUnaryXNorOp, vpiUnaryXNorOp};
  EXPECT_EQ(PropertiesOf(vpiOpType, ProcedureRightSides()), kOps);
}

}  // namespace
}  // namespace delta
