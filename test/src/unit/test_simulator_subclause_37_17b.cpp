#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "fixture_vpi_run.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VariablesOfARun : public VpiDesignRun {
 protected:
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  static int CountOf(int type, vpiHandle ref) {
    int count = 0;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return 0;
    while (vpi_scan(it) != nullptr) ++count;
    return count;
  }

  static vpiHandle Var(const char* name) {
    return vpi_handle_by_name(VpiText(name), nullptr);
  }

  static vpiHandle Named(int type, vpiHandle ref, std::string_view name) {
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return nullptr;
    while (vpiHandle obj = vpi_scan(it)) {
      if (vpi_get_str(vpiName, obj) == name) {
        vpi_free_object(it);
        return obj;
      }
    }
    return nullptr;
  }

  static std::vector<int> IntsOf(int type, vpiHandle ref) {
    std::vector<int> values;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return values;
    while (vpiHandle obj = vpi_scan(it)) values.push_back(IntOf(obj));
    return values;
  }
};

constexpr const char* kPackedVariables =
    "module top;\n"
    "  logic [7:0] v = 8'b0000_1000;\n"
    "  logic [15:10] w = 6'b00_0100;\n"
    "endmodule\n";

TEST_F(VariablesOfARun, APackedVariableHasOneBitPerBit) {
  Run(kPackedVariables);
  EXPECT_EQ(CountOf(vpiBit, Var("top.v")), 8);
}

TEST_F(VariablesOfARun, TheBitAtAnIndexHoldsThatBit) {
  Run(kPackedVariables);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.v"), 3)), 1);
}

TEST_F(VariablesOfARun, TheBitBesideItHoldsItsOwn) {
  Run(kPackedVariables);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.v"), 2)), 0);
}

TEST_F(VariablesOfARun, ABitIsAddressedByTheDeclaredRange) {
  Run(kPackedVariables);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.w"), 12)), 1);
}

TEST_F(VariablesOfARun, ABitsIndexIsItsDeclaredIndex) {
  Run(kPackedVariables);
  EXPECT_EQ(IntOf(vpi_handle(vpiIndex, vpi_handle_by_index(Var("top.w"), 12))),
            12);
}

TEST_F(VariablesOfARun, ABitsSizeIsOne) {
  Run(kPackedVariables);
  EXPECT_EQ(vpi_get(vpiSize, vpi_handle_by_index(Var("top.v"), 3)), 1);
}

TEST_F(VariablesOfARun, ABitsParentIsItsVariable) {
  Run(kPackedVariables);
  EXPECT_STREQ(
      vpi_get_str(vpiName,
                  vpi_handle(vpiParent, vpi_handle_by_index(Var("top.v"), 3))),
      "v");
}

TEST_F(VariablesOfARun, ABitAtAConstantIndexIsAConstantSelect) {
  Run(kPackedVariables);
  EXPECT_EQ(vpi_get(vpiConstantSelect, vpi_handle_by_index(Var("top.v"), 3)),
            1);
}

TEST_F(VariablesOfARun, AStaticVariableWithNoParentIsAConstantSelect) {
  Run(kPackedVariables);
  EXPECT_EQ(vpi_get(vpiConstantSelect, Var("top.v")), 1);
}

TEST_F(VariablesOfARun, WritingABitWritesThatBitOfTheVariable) {
  Run(kPackedVariables);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 1;
  vpi_put_value(vpi_handle_by_index(Var("top.v"), 0), &value, nullptr,
                vpiNoDelay);
  EXPECT_EQ(IntOf(Var("top.v")), 9);
}

constexpr const char* kVariableKinds =
    "typedef enum {A, B} e_t;\n"
    "module top;\n"
    "  e_t e;\n"
    "  int i;\n"
    "  logic [3:0] lv;\n"
    "  logic ls;\n"
    "  string s = \"hello\";\n"
    "  int arr[0:3];\n"
    "  int q[$];\n"
    "  int d[];\n"
    "  int aa[int];\n"
    "  struct {int a; int b;} st;\n"
    "  initial begin\n"
    "    q = '{1, 2, 3};\n"
    "    d = new[5];\n"
    "    aa[1] = 1;\n"
    "    aa[2] = 2;\n"
    "  end\n"
    "endmodule\n";

TEST_F(VariablesOfARun, AnEnumTypedefVariableIsAnEnumVar) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiType, Var("top.e")), vpiEnumVar);
}

TEST_F(VariablesOfARun, AVirtualInterfaceVariableIsAVirtualInterfaceVar) {
  Run("interface ifc; endinterface\n"
      "module top; virtual ifc vi; endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, Var("top.vi")), vpiVirtualInterfaceVar);
}

TEST_F(VariablesOfARun, AnIntIsSigned) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiSigned, Var("top.i")), 1);
}

TEST_F(VariablesOfARun, ALogicVectorIsUnsigned) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiSigned, Var("top.lv")), 0);
}

TEST_F(VariablesOfARun, AStringsSizeIsItsLength) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiSize, Var("top.s")), 5);
}

TEST_F(VariablesOfARun, AStaticArraysSizeIsItsElementCount) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiSize, Var("top.arr")), 4);
}

TEST_F(VariablesOfARun, AQueuesSizeIsItsElementCount) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiSize, Var("top.q")), 3);
}

TEST_F(VariablesOfARun, ADynamicArraysSizeIsItsElementCount) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiSize, Var("top.d")), 5);
}

TEST_F(VariablesOfARun, AnAssociativeArraysSizeIsItsEntryCount) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiSize, Var("top.aa")), 2);
}

TEST_F(VariablesOfARun, AnUnpackedStructsSizeIsItsFieldCount) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiSize, Var("top.st")), 2);
}

TEST_F(VariablesOfARun, APackedLogicIsAVector) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiVector, Var("top.lv")), 1);
}

TEST_F(VariablesOfARun, AnUnpackedLogicIsAScalar) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiScalar, Var("top.ls")), 1);
}

TEST_F(VariablesOfARun, AnIntIsAVector) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiVector, Var("top.i")), 1);
}

TEST_F(VariablesOfARun, AFixedArrayIsAStaticArray) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiArrayType, Var("top.arr")), vpiStaticArray);
}

TEST_F(VariablesOfARun, AQueueIsAQueueArray) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiArrayType, Var("top.q")), vpiQueueArray);
}

TEST_F(VariablesOfARun, ADynamicArrayIsADynamicArray) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiArrayType, Var("top.d")), vpiDynamicArray);
}

TEST_F(VariablesOfARun, AnAssociativeArrayIsAnAssocArray) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiArrayType, Var("top.aa")), vpiAssocArray);
}

constexpr const char* kAggregateTypedefs =
    "typedef struct { int a; int b; } s_t;\n"
    "typedef union { int a; shortint b; } u_t;\n"
    "module top; s_t s; u_t u; endmodule\n";

TEST_F(VariablesOfARun, AStructTypedefVariableIsAStructVar) {
  Run(kAggregateTypedefs);
  EXPECT_EQ(vpi_get(vpiType, Var("top.s")), vpiStructVar);
}

TEST_F(VariablesOfARun, AUnionTypedefVariableIsAUnionVar) {
  Run(kAggregateTypedefs);
  EXPECT_EQ(vpi_get(vpiType, Var("top.u")), vpiUnionVar);
}

TEST_F(VariablesOfARun, AStructTypedefVariablesSizeIsItsFieldCount) {
  Run(kAggregateTypedefs);
  EXPECT_EQ(vpi_get(vpiSize, Var("top.s")), 2);
}

constexpr const char* kDeclaredBases =
    "module top;\n"
    "  byte b;\n"
    "  enum logic {L0, L1} el;\n"
    "  enum logic [1:0] {V0, V1} ev;\n"
    "  enum int {I0, I1} ei;\n"
    "  int fixed_of_dynamic [2][];\n"
    "  struct {int a;} structs [3];\n"
    "endmodule\n";

TEST_F(VariablesOfARun, AByteIsAVector) {
  Run(kDeclaredBases);
  EXPECT_EQ(vpi_get(vpiVector, Var("top.b")), 1);
}

TEST_F(VariablesOfARun, AnEnumOfAScalarLogicBaseIsAScalar) {
  Run(kDeclaredBases);
  EXPECT_EQ(vpi_get(vpiScalar, Var("top.el")), 1);
  EXPECT_EQ(vpi_get(vpiVector, Var("top.el")), 0);
}

TEST_F(VariablesOfARun, AnEnumOfAPackedLogicBaseIsAVector) {
  Run(kDeclaredBases);
  EXPECT_EQ(vpi_get(vpiVector, Var("top.ev")), 1);
  EXPECT_EQ(vpi_get(vpiScalar, Var("top.ev")), 0);
}

TEST_F(VariablesOfARun, AnEnumOfAnIntBaseIsAVector) {
  Run(kDeclaredBases);
  EXPECT_EQ(vpi_get(vpiVector, Var("top.ei")), 1);
  EXPECT_EQ(vpi_get(vpiScalar, Var("top.ei")), 0);
}

TEST_F(VariablesOfARun, AFixedArrayOfDynamicArraysCountsItsLeftDimension) {
  Run(kDeclaredBases);
  EXPECT_EQ(vpi_get(vpiArrayType, Var("top.fixed_of_dynamic")), vpiStaticArray);
  EXPECT_EQ(vpi_get(vpiSize, Var("top.fixed_of_dynamic")), 2);
}

TEST_F(VariablesOfARun, AnArrayOfStructsCountsItsElements) {
  Run(kDeclaredBases);
  EXPECT_EQ(vpi_get(vpiType, Var("top.structs")), vpiRegArray);
  EXPECT_EQ(vpi_get(vpiSize, Var("top.structs")), 3);
}

constexpr const char* kPackedAggregates =
    "module top;\n"
    "  logic [1:0][3:0] m = 8'b0000_0100;\n"
    "  struct packed { logic [3:0] a; logic [3:0] b; } s = 8'h5A;\n"
    "  union packed { logic [7:0] a; bit [7:0] b; } u;\n"
    "endmodule\n";

TEST_F(VariablesOfARun, AMultidimensionalPackedArrayHasOneBitPerBit) {
  Run(kPackedAggregates);
  EXPECT_EQ(CountOf(vpiBit, Var("top.m")), 8);
}

TEST_F(VariablesOfARun, AMultidimensionalPackedBitIsNamedByEveryIndex) {
  Run(kPackedAggregates);
  vpiHandle it = vpi_iterate(vpiBit, Var("top.m"));
  ASSERT_NE(it, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_scan(it)), "m[1][3]");
  vpi_free_object(it);
}

TEST_F(VariablesOfARun, AMultidimensionalPackedBitHoldsItsBit) {
  Run(kPackedAggregates);
  EXPECT_EQ(IntOf(Named(vpiBit, Var("top.m"), "m[0][2]")), 1);
}

TEST_F(VariablesOfARun, TheMultidimensionalPackedBitBesideItHoldsItsOwn) {
  Run(kPackedAggregates);
  EXPECT_EQ(IntOf(Named(vpiBit, Var("top.m"), "m[1][2]")), 0);
}

TEST_F(VariablesOfARun, AMultidimensionalPackedBitsIndexIsTheInnermost) {
  Run(kPackedAggregates);
  EXPECT_EQ(IntOf(vpi_handle(vpiIndex, Named(vpiBit, Var("top.m"), "m[0][2]"))),
            2);
}

TEST_F(VariablesOfARun, AMultidimensionalPackedBitsIndicesRunOutward) {
  Run(kPackedAggregates);
  EXPECT_EQ(IntsOf(vpiIndex, Named(vpiBit, Var("top.m"), "m[0][2]")),
            (std::vector<int>{2, 0}));
}

TEST_F(VariablesOfARun, APackedStructHasOneBitPerBit) {
  Run(kPackedAggregates);
  EXPECT_EQ(CountOf(vpiBit, Var("top.s")), 8);
}

TEST_F(VariablesOfARun, APackedStructsBitHoldsItsBit) {
  Run(kPackedAggregates);
  EXPECT_EQ(IntOf(Named(vpiBit, Var("top.s"), "s[4]")), 1);
}

TEST_F(VariablesOfARun, APackedStructsBitBesideItHoldsItsOwn) {
  Run(kPackedAggregates);
  EXPECT_EQ(IntOf(Named(vpiBit, Var("top.s"), "s[5]")), 0);
}

TEST_F(VariablesOfARun, APackedUnionHasOneBitPerBit) {
  Run(kPackedAggregates);
  EXPECT_EQ(CountOf(vpiBit, Var("top.u")), 8);
}

constexpr const char* kDimensions =
    "module top;\n"
    "  logic [7:0] v;\n"
    "  logic [1:0][3:0] m;\n"
    "  int arr[3:6];\n"
    "  int md[2][3];\n"
    "  int q[$];\n"
    "endmodule\n";

std::vector<int> LeftBoundsOf(vpiHandle ref) {
  std::vector<int> bounds;
  vpiHandle it = vpi_iterate(vpiRange, ref);
  if (it == nullptr) return bounds;
  while (vpiHandle range = vpi_scan(it)) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(vpi_handle(vpiLeftRange, range), &value);
    bounds.push_back(value.value.integer);
  }
  return bounds;
}

TEST_F(VariablesOfARun, APackedVariablesLeftRangeIsItsLeftBound) {
  Run(kDimensions);
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, Var("top.v"))), 7);
}

TEST_F(VariablesOfARun, APackedVariablesRightRangeIsItsRightBound) {
  Run(kDimensions);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, Var("top.v"))), 0);
}

TEST_F(VariablesOfARun, AnArraysLeftRangeIsItsLeftUnpackedBound) {
  Run(kDimensions);
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, Var("top.arr"))), 3);
}

TEST_F(VariablesOfARun, AnArraysRightRangeIsItsRightUnpackedBound) {
  Run(kDimensions);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, Var("top.arr"))), 6);
}

TEST_F(VariablesOfARun, AQueuesLeftRangeIsNull) {
  Run(kDimensions);
  EXPECT_EQ(vpi_handle(vpiLeftRange, Var("top.q")), nullptr);
}

TEST_F(VariablesOfARun, AnArraysRangesAreItsUnpackedDimensions) {
  Run(kDimensions);
  EXPECT_EQ(LeftBoundsOf(Var("top.md")), (std::vector<int>{0, 0}));
}

TEST_F(VariablesOfARun, ARangesSizeIsItsElementCount) {
  Run(kDimensions);
  vpiHandle it = vpi_iterate(vpiRange, Var("top.md"));
  ASSERT_NE(it, nullptr);
  vpi_scan(it);
  EXPECT_EQ(vpi_get(vpiSize, vpi_scan(it)), 3);
  vpi_free_object(it);
}

TEST_F(VariablesOfARun, AQueuesRangeIsEmpty) {
  Run(kDimensions);
  EXPECT_EQ(CountOf(vpiRange, Var("top.q")), 1);
}

TEST_F(VariablesOfARun, APackedArraysRangesAreItsPackedDimensions) {
  Run(kDimensions);
  EXPECT_EQ(LeftBoundsOf(Var("top.m")), (std::vector<int>{1, 3}));
}

constexpr const char* kFixedArrays =
    "module top;\n"
    "  int arr[0:3];\n"
    "  int m[2][3];\n"
    "  initial begin\n"
    "    arr[2] = 7;\n"
    "    m[1][2] = 9;\n"
    "  end\n"
    "endmodule\n";

TEST_F(VariablesOfARun, AnArrayElementIsReachedByIndex) {
  Run(kFixedArrays);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.arr"), 2)), 7);
}

TEST_F(VariablesOfARun, AnArrayElementIsAnArrayMember) {
  Run(kFixedArrays);
  EXPECT_EQ(vpi_get(vpiArrayMember, vpi_handle_by_index(Var("top.arr"), 2)), 1);
}

TEST_F(VariablesOfARun, AnArrayElementsParentIsTheArray) {
  Run(kFixedArrays);
  EXPECT_STREQ(
      vpi_get_str(vpiName, vpi_handle(vpiParent,
                                      vpi_handle_by_index(Var("top.arr"), 2))),
      "arr");
}

TEST_F(VariablesOfARun, AnArrayElementIsReachedByName) {
  Run(kFixedArrays);
  EXPECT_EQ(IntOf(Var("top.arr[2]")), 7);
}

TEST_F(VariablesOfARun, AStaticArrayElementIsAConstantSelect) {
  Run(kFixedArrays);
  EXPECT_EQ(vpi_get(vpiConstantSelect, vpi_handle_by_index(Var("top.arr"), 2)),
            1);
}

TEST_F(VariablesOfARun, AnElementOfASubarrayIsReachedByIndex) {
  Run(kFixedArrays);
  EXPECT_EQ(IntOf(vpi_handle_by_index(vpi_handle_by_index(Var("top.m"), 1), 2)),
            9);
}

TEST_F(VariablesOfARun, ASubarrayIsAnArrayVar) {
  Run(kFixedArrays);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle_by_index(Var("top.m"), 1)),
            vpi_get(vpiType, Var("top.m")));
}

TEST_F(VariablesOfARun, AnElementOfAMultidimensionalArrayIsReachedByIndices) {
  Run(kFixedArrays);
  PLI_INT32 indices[] = {1, 2};
  EXPECT_EQ(IntOf(vpi_handle_by_multi_index(Var("top.m"), 2, indices)), 9);
}

TEST_F(VariablesOfARun, AnElementsIndicesRunOutward) {
  Run(kFixedArrays);
  EXPECT_EQ(IntsOf(vpiIndex, Var("top.m[1][2]")), (std::vector<int>{2, 1}));
}

constexpr const char* kVariableSizedArrays =
    "module top;\n"
    "  int q[$];\n"
    "  int d[];\n"
    "  int aa[int];\n"
    "  initial begin\n"
    "    q = '{4, 5, 6};\n"
    "    d = new[5];\n"
    "    d[4] = 8;\n"
    "    aa[10] = 3;\n"
    "  end\n"
    "endmodule\n";

TEST_F(VariablesOfARun, AQueueElementIsReachedByIndex) {
  Run(kVariableSizedArrays);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.q"), 1)), 5);
}

TEST_F(VariablesOfARun, ADynamicArrayElementIsReachedByIndex) {
  Run(kVariableSizedArrays);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.d"), 4)), 8);
}

TEST_F(VariablesOfARun, AnAssociativeArrayElementIsReachedByKey) {
  Run(kVariableSizedArrays);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.aa"), 10)), 3);
}

TEST_F(VariablesOfARun, AnIndexPastAQueuesEndReachesNothing) {
  Run(kVariableSizedArrays);
  EXPECT_EQ(vpi_handle_by_index(Var("top.q"), 7), nullptr);
}

TEST_F(VariablesOfARun, AQueueElementIsAnArrayMember) {
  Run(kVariableSizedArrays);
  EXPECT_EQ(vpi_get(vpiArrayMember, vpi_handle_by_index(Var("top.q"), 1)), 1);
}

TEST_F(VariablesOfARun, AQueueElementIsNoConstantSelect) {
  Run(kVariableSizedArrays);
  EXPECT_EQ(vpi_get(vpiConstantSelect, vpi_handle_by_index(Var("top.q"), 1)),
            0);
}

TEST_F(VariablesOfARun, WritingAQueueElementWritesTheQueue) {
  Run(kVariableSizedArrays);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 9;
  vpi_put_value(vpi_handle_by_index(Var("top.q"), 0), &value, nullptr,
                vpiNoDelay);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.q"), 0)), 9);
}

constexpr const char* kUnpackedStruct =
    "module top;\n"
    "  struct {int a; int b;} s = '{5, 6};\n"
    "endmodule\n";

TEST_F(VariablesOfARun, AnUnpackedStructHasAMemberPerField) {
  Run(kUnpackedStruct);
  EXPECT_EQ(NamesOf(vpiMember, Var("top.s")),
            (std::vector<std::string>{"a", "b"}));
}

TEST_F(VariablesOfARun, AStructMemberHoldsItsFieldsValue) {
  Run(kUnpackedStruct);
  EXPECT_EQ(IntOf(Var("top.s.b")), 6);
}

TEST_F(VariablesOfARun, TheStructMemberBesideItHoldsItsOwn) {
  Run(kUnpackedStruct);
  EXPECT_EQ(IntOf(Var("top.s.a")), 5);
}

TEST_F(VariablesOfARun, AStructMembersParentIsTheStruct) {
  Run(kUnpackedStruct);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiParent, Var("top.s.b"))),
               "s");
}

TEST_F(VariablesOfARun, AStructMemberIsAConstantSelect) {
  Run(kUnpackedStruct);
  EXPECT_EQ(vpi_get(vpiConstantSelect, Var("top.s.b")), 1);
}

TEST_F(VariablesOfARun, AStructMembersKindIsItsFieldsType) {
  Run(kUnpackedStruct);
  EXPECT_EQ(vpi_get(vpiType, Var("top.s.b")), vpiIntVar);
}

TEST_F(VariablesOfARun, AStructMembersOfNonIntegralTypesHaveTheirKinds) {
  Run("module top;\n"
      "  typedef enum {X, Y} e_t;\n"
      "  struct {real r; shortreal sr; string s; enum {A, B} en; e_t te;} m;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, Var("top.m.r")), vpiRealVar);
  EXPECT_EQ(vpi_get(vpiType, Var("top.m.sr")), vpiShortRealVar);
  EXPECT_EQ(vpi_get(vpiType, Var("top.m.s")), vpiStringVar);
  EXPECT_EQ(vpi_get(vpiType, Var("top.m.en")), vpiEnumVar);
  EXPECT_EQ(vpi_get(vpiType, Var("top.m.te")), vpiEnumVar);
}

TEST_F(VariablesOfARun, ARealStructMemberHoldsARealValue) {
  Run("module top; struct {int a; real r;} m = '{1, 2.5}; endmodule\n");
  s_vpi_value value = {};
  value.format = vpiObjTypeVal;
  vpi_get_value(Var("top.m.r"), &value);
  EXPECT_EQ(value.format, vpiRealVal);
  EXPECT_DOUBLE_EQ(value.value.real, 2.5);
}

TEST_F(VariablesOfARun, WritingAStructMemberWritesItsField) {
  Run(kUnpackedStruct);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 9;
  vpi_put_value(Var("top.s.a"), &value, nullptr, vpiNoDelay);
  EXPECT_EQ(IntOf(Var("top.s.a")), 9);
}

TEST_F(VariablesOfARun, WritingAStructMemberLeavesTheOtherField) {
  Run(kUnpackedStruct);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 9;
  vpi_put_value(Var("top.s.a"), &value, nullptr, vpiNoDelay);
  EXPECT_EQ(IntOf(Var("top.s.b")), 6);
}

constexpr const char* kTypedefs =
    "typedef enum {X, Y} ue_t;\n"
    "module top;\n"
    "  typedef enum {A, B, C} e_t;\n"
    "  typedef struct { int a; int b; } s_t;\n"
    "  e_t e;\n"
    "  s_t s;\n"
    "  ue_t u;\n"
    "endmodule\n";

TEST_F(VariablesOfARun, AModulesTypedefsAreTypespecs) {
  Run(kTypedefs);
  EXPECT_EQ(NamesOf(vpiTypedef, Var("top")),
            (std::vector<std::string>{"e_t", "s_t"}));
}

TEST_F(VariablesOfARun, AnEnumTypespecHasItsConstants) {
  Run(kTypedefs);
  EXPECT_EQ(NamesOf(vpiEnumConst, Named(vpiTypedef, Var("top"), "e_t")),
            (std::vector<std::string>{"A", "B", "C"}));
}

TEST_F(VariablesOfARun, AnEnumConstHoldsItsValue) {
  Run(kTypedefs);
  EXPECT_EQ(
      IntOf(Named(vpiEnumConst, Named(vpiTypedef, Var("top"), "e_t"), "C")), 2);
}

TEST_F(VariablesOfARun, AStructTypespecHasItsMembers) {
  Run(kTypedefs);
  EXPECT_EQ(NamesOf(vpiTypespecMember, Named(vpiTypedef, Var("top"), "s_t")),
            (std::vector<std::string>{"a", "b"}));
}

TEST_F(VariablesOfARun, AnEnumVariablesTypespecIsItsTypedefs) {
  Run(kTypedefs);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiTypespec, Var("top.e"))),
               "e_t");
}

TEST_F(VariablesOfARun, AStructVariablesTypespecIsItsTypedefs) {
  Run(kTypedefs);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiTypespec, Var("top.s"))),
               "s_t");
}

TEST_F(VariablesOfARun, AVariablesTypespecIsTheUnitsTypedef) {
  Run(kTypedefs);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiTypespec, Var("top.u"))),
               "ue_t");
}

vpiHandle RhsDriving(const char* target) {
  vpiHandle lhs = vpi_handle_by_name(VpiText(target), nullptr);
  vpiHandle it =
      vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
  while (vpiHandle assign = it == nullptr ? nullptr : vpi_scan(it)) {
    if (VpiObjectOf(vpi_handle(vpiLhs, assign)) == VpiObjectOf(lhs)) {
      return vpi_handle(vpiRhs, assign);
    }
  }
  return nullptr;
}

constexpr const char* kPackedSelects =
    "module top; logic [3:0][7:0] m = 32'h44332211; integer i = 1;\n"
    "  wire [7:0] y, z; wire b;\n"
    "  assign y = m[i]; assign z = m[2]; assign b = m[2][1];\n"
    "endmodule\n";

TEST_F(VariablesOfARun, AVaryingOuterPackedSelectIsAVectorOfItsElement) {
  Run(kPackedSelects);
  vpiHandle rhs = RhsDriving("top.y");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiLogicVar);
  EXPECT_EQ(vpi_get(vpiSize, rhs), 8);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, rhs)), VpiObjectOf(Var("top.m")));
  EXPECT_EQ(IntOf(rhs), 0x22);
}

TEST_F(VariablesOfARun, AConstantOuterPackedSelectIsNamedByItsIndex) {
  Run(kPackedSelects);
  vpiHandle rhs = RhsDriving("top.z");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiLogicVar);
  EXPECT_EQ(vpi_get(vpiSize, rhs), 8);
  EXPECT_STREQ(vpi_get_str(vpiName, rhs), "m[2]");
  EXPECT_EQ(IntOf(rhs), 0x33);
}

TEST_F(VariablesOfARun, ASelectOfEveryPackedDimensionIsItsVarBit) {
  Run(kPackedSelects);
  vpiHandle rhs = RhsDriving("top.b");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiRegBit);
  EXPECT_STREQ(vpi_get_str(vpiName, rhs), "m[2][1]");
  EXPECT_EQ(IntOf(rhs), 1);
}

TEST_F(VariablesOfARun, AValuePutToAnOuterPackedSelectLandsInItsElement) {
  Run(kPackedSelects);
  vpiHandle constant = RhsDriving("top.z");
  vpiHandle varying = RhsDriving("top.y");
  ASSERT_NE(constant, nullptr);
  ASSERT_NE(varying, nullptr);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 0x55;
  vpi_put_value(constant, &value, nullptr, vpiNoDelay);
  value.value.integer = 0x66;
  vpi_put_value(varying, &value, nullptr, vpiNoDelay);
  EXPECT_EQ(IntOf(Var("top.m")), 0x44556611);
}

TEST_F(VariablesOfARun, AGenerateBlockVariableIsNamedUnderItsGenScope) {
  Run("module top;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    int v;\n"
      "    initial v = 7 + i;\n"
      "  end\n"
      "endmodule\n");
  vpiHandle v = Var("top.g[1].v");
  ASSERT_NE(v, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, v), "v");
  EXPECT_STREQ(vpi_get_str(vpiFullName, v), "top.g[1].v");
  EXPECT_EQ(IntOf(v), 8);
  EXPECT_EQ(Named(vpiVariables, Var("top.g[1]"), "v"), v);
  EXPECT_EQ(CountOf(vpiVariables, Var("top")), 0);
}

TEST_F(VariablesOfARun, AnAnsiVariablePortsVariableIsTheKindOfItsType) {
  Run("module sub(output integer i, output int j, output logic [3:0] l,\n"
      "           output real r);\n"
      "endmodule\n"
      "module top; integer a; int b; logic [3:0] c; real d;\n"
      "  sub u(.i(a), .j(b), .l(c), .r(d));\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.u.i")), vpiIntegerVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.u.j")), vpiIntVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.u.l")), vpiReg);
  EXPECT_EQ(vpi_get(vpiType, By("top.u.r")), vpiRealVar);
}

TEST(VariableKindModel, AModulesVariablesAreItsBodysAndItsVariablePorts) {
  RtlirModule mod;
  RtlirVariable body;
  body.name = "s";
  mod.variables.push_back(body);
  const std::vector<std::pair<std::string_view, DataTypeKind>> kPorts = {
      {"s", DataTypeKind::kStruct},
      {"t", DataTypeKind::kRealtime},
      {"u", DataTypeKind::kString},
      {"n", DataTypeKind::kLogic},
      {"f", DataTypeKind::kNamed}};
  for (const auto& [name, kind] : kPorts) {
    RtlirPort& port = mod.ports.emplace_back();
    port.name = name;
    port.data_kind = kind;
  }
  mod.ports[3].net_type = NetType::kWire;
  mod.ports[4].is_interface_port = true;
  const std::vector<RtlirVariable> kVars = VpiDeclaredVariables(mod);
  ASSERT_EQ(kVars.size(), 3U);
  EXPECT_EQ(kVars[0].name, "s");
  EXPECT_EQ(kVars[1].name, "t");
  EXPECT_TRUE(kVars[1].is_real);
  EXPECT_FALSE(kVars[1].is_string);
  EXPECT_EQ(kVars[2].name, "u");
  EXPECT_TRUE(kVars[2].is_string);
  EXPECT_FALSE(kVars[2].is_real);
}

}  // namespace
}  // namespace delta
