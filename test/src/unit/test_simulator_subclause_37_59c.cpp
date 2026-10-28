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

// A design whose one continuous assignment's right side is the expression a
// case is about.
class AssignedExpressionsOfARun : public VpiDesignRun {
 protected:
  // The right side of the top's continuous assignment.
  static vpiHandle Rhs() {
    vpiHandle it = vpi_iterate(vpiContAssign, By("top"));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiRhs, vpi_scan(it));
  }

  // The integer value of an expression object, -1 where none is written.
  static int IntOf(vpiHandle expr) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = -1;
    vpi_get_value(expr, &value);
    return value.value.integer;
  }

  // The operands of an operation, in order.
  static std::vector<vpiHandle> OperandsOf(vpiHandle op) {
    std::vector<vpiHandle> operands;
    vpiHandle it = vpi_iterate(vpiOperand, op);
    if (it == nullptr) return operands;
    while (vpiHandle operand = vpi_scan(it)) operands.push_back(operand);
    return operands;
  }

  // The integer values of `exprs`, in order.
  static std::vector<int> ValuesOf(const std::vector<vpiHandle>& exprs) {
    std::vector<int> values;
    values.reserve(exprs.size());
    for (vpiHandle expr : exprs) values.push_back(IntOf(expr));
    return values;
  }

  // The integer property `property` of each of `exprs`, in order.
  static std::vector<int> PropertiesOf(int property,
                                       const std::vector<vpiHandle>& exprs) {
    std::vector<int> values;
    values.reserve(exprs.size());
    for (vpiHandle expr : exprs) values.push_back(vpi_get(property, expr));
    return values;
  }

  // The right sides of the assignments top's one procedure runs, in order.
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

// Detail 9: a part select is a constant select when its parent is, the parent
// has static bounds and both bounds are elaboration-time constants.
TEST_F(AssignedExpressionsOfARun, APartSelectWithConstantBoundsIsConstant) {
  Run("module top; logic [7:0] r; wire [3:0] w; assign w = r[3:0];\n"
      "endmodule\n");
  vpiHandle select = Rhs();
  ASSERT_NE(select, nullptr);
  ASSERT_EQ(vpi_get(vpiType, select), vpiPartSelect);
  EXPECT_EQ(vpi_get(vpiConstantSelect, select), 1);
}

// Detail 9: an indexed part select whose base varies is not.
TEST_F(AssignedExpressionsOfARun, AnIndexedPartSelectWithAVaryingBaseIsNot) {
  Run("module top; logic [7:0] r; logic [2:0] i; wire [3:0] w;\n"
      "  assign w = r[i+:4];\n"
      "endmodule\n");
  vpiHandle select = Rhs();
  ASSERT_NE(select, nullptr);
  ASSERT_EQ(vpi_get(vpiType, select), vpiIndexedPartSelect);
  EXPECT_EQ(vpi_get(vpiConstantSelect, select), 0);
}

// Detail 9 read off objects standing in no design. A part select reaching no
// parent is no constant select, nor is one whose parent is none, an element
// of a dynamic array (§37.17 detail 27). Into an array, the parent's bounds
// must be static, so one into a static array var is and one into a dynamic
// array is not. Each range expression must be an elaboration-time constant,
// so a variable written as either bound, or as the width, makes it none.
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

// Details 3 and 5: a cast is a unary operation whose typespec is the type it
// casts to, a built-in type a keyword names...
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

// ...or a typedef the module declares.
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

// The typespec a cast relates to, null for none.
vpiHandle CastTypespec(vpiHandle cast) {
  if (cast == nullptr || vpi_get(vpiOpType, cast) != vpiCastOp) return nullptr;
  return vpi_handle(vpiTypespec, cast);
}

// The typespec kinds of the casts `rights` are, 0 for one with none.
std::vector<int> CastTypespecKinds(const std::vector<vpiHandle>& rights) {
  std::vector<int> kinds;
  kinds.reserve(rights.size());
  for (vpiHandle right : rights) {
    vpiHandle typespec = CastTypespec(right);
    kinds.push_back(typespec != nullptr ? vpi_get(vpiType, typespec) : 0);
  }
  return kinds;
}

// The number of elements the first range `typespec` reaches holds, 0 for a
// typespec reaching none.
int FirstRangeSize(vpiHandle typespec) {
  vpiHandle ranges = vpi_iterate(vpiRange, typespec);
  if (ranges == nullptr) return 0;
  const int kSize = vpi_get(vpiSize, vpi_scan(ranges));
  vpi_release_handle(ranges);
  return kSize;
}

// ...or, for a size cast, a vector keeping the operand's 2-state nature
// (§6.24.1)...
TEST_F(AssignedExpressionsOfARun, ASizeCastOfATwoStateOperandIsABitVector) {
  Run("module top; int i; wire [7:0] w; assign w = 8'(i); endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiBitTypespec);
}

// ...or its 4-state nature...
TEST_F(AssignedExpressionsOfARun, ASizeCastOfAFourStateOperandIsALogicVector) {
  Run("module top; logic [3:0] r; wire [7:0] w; assign w = 8'(r);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiLogicTypespec);
}

// ...an operation's being 2-state where every operand is (§11.8.1)...
TEST_F(AssignedExpressionsOfARun, ASizeCastOfATwoStateOperationIsABitVector) {
  Run("module top; int i, j; wire [7:0] w; assign w = 8'(i + j);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiBitTypespec);
}

// ...and 4-state where one is not...
TEST_F(AssignedExpressionsOfARun, ASizeCastOfAMixedOperationIsALogicVector) {
  Run("module top; int i; logic [3:0] r; wire [7:0] w;\n"
      "  assign w = 8'(i + r);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiLogicTypespec);
}

// ...a select being as its vector is, 2-state from a bit vector and 4-state
// from a logic vector, a var select or an array net element, as is a bit,
// byte, shortint or longint variable 2-state; an operation none of whose
// operands has an object, such as a logical equivalence (§11.4.7), which no
// operation type names, is any expression it cannot judge, 4-state...
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

// ...as wide as its size expression's value, a parameter's included...
TEST_F(AssignedExpressionsOfARun, ASizeCastIsAsWideAsItsSizeExpression) {
  Run("module top; localparam W = 6; logic [3:0] r; wire [7:0] w;\n"
      "  assign w = W'(r);\n"
      "endmodule\n");
  ASSERT_NE(CastTypespec(Rhs()), nullptr);
  EXPECT_EQ(vpi_get(vpiSize, Rhs()), 6);
}

// ...or, for a signing cast, the operand's type of the signedness it names...
TEST_F(AssignedExpressionsOfARun, ASigningCastIsTheOperandsTypeSigned) {
  Run("module top; logic [7:0] r; wire [7:0] w; assign w = signed'(r);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiLogicTypespec);
  EXPECT_EQ(vpi_get(vpiSigned, typespec), 1);
}

// ...unsigned where it names that...
TEST_F(AssignedExpressionsOfARun, AnUnsigningCastIsTheOperandsTypeUnsigned) {
  Run("module top; int i; wire [31:0] w; assign w = unsigned'(i);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiIntTypespec);
  EXPECT_EQ(vpi_get(vpiSigned, typespec), 0);
}

// ...or, for a const cast, the operand's own type.
TEST_F(AssignedExpressionsOfARun, AConstCastIsTheOperandsType) {
  Run("module top; int i; wire [31:0] w; assign w = const'(i); endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiIntTypespec);
}

// A cast to a type parameter (§6.20.3) has the typespec of the type the
// instance gives it, not the default its declaration writes.
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

// A cast to a type reference (§6.23) has the typespec of the type it refers
// to: of a variable it names, the type the variable was declared with, a bit
// vector of four bits or a byte; of a typedef it names, the typedef's; of a
// built-in type it writes, that type over the range written, twelve bits; and
// of an operation, its self-determined type, a 2-state vector where every
// operand is 2-state (§11.8.1).
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

// A cast to a typedef a package declares has its typespec, whether it names
// the typedef through the package (§26.3) or a wildcard or an explicit import
// makes it visible; and so does a cast to one the compilation unit declares
// (§3.12.1), which a name finds after the imports' (§26.3).
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

// A cast in a variable's initialization expression (§37.17 detail 8), which
// its instance writes in no scope of its own, has the typespec of a built-in
// type it names and of a typedef its module declares, found from the
// instance.
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

// A cast in a variable's initialization expression finds a typedef a package
// declares, named through the package or made visible by an import (§26.3),
// and one the compilation unit declares (§3.12.1), as one in a procedure does.
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

// A cast in the first top module's variable initializer finds a typedef the
// top declares (§6.18), though the top's instance is keyed under its name
// rather than under the empty prefix its expressions are written with.
TEST_F(AssignedExpressionsOfARun,
       ACastInTheFirstTopsInitializerFindsItsTypedef) {
  Run("module top; typedef bit [3:0] nib_t; logic [7:0] r;\n"
      "  logic [3:0] v = nib_t'(r);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(vpi_handle(vpiExpr, By("top.v")));
  ASSERT_NE(typespec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "nib_t");
}

// A size cast is as wide as the constant its width is, an operation over a
// parameter, a call of $bits on a variable or a package's parameter written
// through the package among them (§11.2.1).
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

// A cast of an expression the model builds no object for, a logical
// equivalence (§11.4.7) having no operation type, takes its nature as 4-state
// and its width and signedness from its value: a size cast is a logic vector
// as wide as its width, and a signing or const cast a logic vector as wide as
// the one bit the equivalence is, of the signedness the signing cast names.
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

// A size cast of an element of an unpacked array of a 2-state type is a bit
// vector, whether the array is fixed, a queue, a dynamic array or an
// associative array (§7.4, §7.10, §7.5, §7.8), and so is one of a bit of such
// an element; of an element of an array of a 4-state type, a logic vector.
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

// A size cast of a packed structure or union is a bit vector where every
// member is 2-state (§7.2.1, §7.3.1), of an enumeration where its base type,
// int by default, is (§6.19), and of a packed array of a 2-state structure
// (§7.4.1); of a structure with a 4-state member, a logic vector.
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

// A size cast of a structure with a 4-state member that a task declares as
// its argument, a variable the run keeps no storage of its own for, is a
// logic vector.
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

// A size cast of a structure all of whose members are 2-state is a bit vector
// (§7.2.1) wherever the structure is declared: as a task's argument or a
// function's local, variables the run keeps no storage of their own for, and
// as the member of a structure, whose storage is a copy of the member's bits.
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

// Every expression has vpiSize, an operation's being its self-determined
// width (§11.6.1): a bitwise and is as wide as its wider operand, and an
// equality is one bit.
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

// A cast to a built-in type a keyword names is as wide as that type (§6.11
// Table 6-8): byte 8 bits, shortint 16, integer 32, and longint and time 64.
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

// A conditional is as wide as the wider of its two results (§11.6.1 Table
// 11-21), which only its three operands tell. Neither Annex K nor Annex M
// names an operation type for the logical equivalence a <-> b (§11.4.7), so
// that operand has no object, the conditional has two operands, and it is
// left unsized rather than sized from the wrong ones.
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

// A part select is as wide as its bounds span, and an indexed part select as
// its width.
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

// So are they, and a replication by its count (§11.4.12.1), where the bounds,
// width or count read parameters or combine constants with an operator, as a
// constant expression may (§11.2.1): a[W-1:0] is 4 bits, a[4:P] 3, a[i+:W+1]
// 5, and {N{b}} 6.
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

// So does any other constant §11.2.1 admits there, which the run values where
// the source wrote it: $bits of a variable (§20.6.2) as a replication's count,
// and a constant function call (§13.4.3) as a part select's bound.
// {$bits(b){c}} is 8 bits and a[f():0] 4.
TEST_F(AssignedExpressionsOfARun, ConstantsTheRunValuesSizeTheirExpressions) {
  Run("module top; function automatic int f(); return 3; endfunction\n"
      "  logic [3:0] b; logic [1:0] c; logic [7:0] a, x;\n"
      "  initial begin x = {$bits(b){c}}; x = a[f():0]; end\n"
      "endmodule\n");
  EXPECT_EQ(PropertiesOf(vpiSize, ProcedureRightSides()),
            (std::vector<int>{8, 4}));
}

// A bit select and a part select hold no storage of their own; each reads the
// bits it selects out of its parent's value.
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

// Detail 6: a keyed pattern nested in a keyed pattern keeps its place, laid
// out positionally by the subarray it fills, nesting preserved. §10.8 lets no
// untyped pattern be a default key's value, so each subarray is keyed.
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

// Detail 10 with Table 37-1: the parent of r[i+1][3][j+:2] is r[i+1][3], a
// select of one packed element out of the element r[i+1] selects, whose own
// parent is that var select.
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

// §11.4.2: a design whose one procedure steps i within the right side of each
// of four assignments, in each of the four forms an increment or decrement
// takes.
constexpr const char* kSteppedRightSides =
    "module top; int i, a, b, c, d;\n"
    "  initial begin a = i++; b = ++i; c = i--; d = --i; end\n"
    "endmodule\n";

// An increment or decrement written within an expression is an operation
// whose operator names which of the four forms it takes and whose one operand
// is the variable it steps (#7280).
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

// Detail 2: each decompiles to the form it was written in, its operator one
// space from the variable it steps (#7281).
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

// Detail 2: a stepped variable that is a select keeps its brackets and needs
// no parentheses, and an operator before a postfix step takes it whole.
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

// §37.59 with §11.4: an expression written with a binary operator is an
// operation reporting that operator's own vpiOpType, the two spellings of
// exclusive nor (§11.4.8) reporting the one constant.
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

// §37.59 with §11.4: so is one written with a prefix unary operator, unary
// plus and each reduction (§11.4.9) among them, both spellings of the
// reduction exclusive nor reporting the one constant.
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
