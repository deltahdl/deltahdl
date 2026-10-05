#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.17 Variables, read off the VPI model a run builds from an elaborated
// design: the variable objects AttachDesignToPliApplications makes, their
// bits, elements, members, ranges and typespecs.

// A design run with a PLI application registered, its variables read back
// once the run is over.
class VariablesOfARun : public VpiDesignRun {
 protected:
  // The integer value of an object.
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  // How many objects of `type` `ref` reaches.
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

  // The object of `type` `ref` reaches under the name `name`, or null.
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

  // The integer values of the objects of `type` `ref` reaches, in order.
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

// §37.17 details 12 and 13: a packed logic variable has one var bit per bit.
TEST_F(VariablesOfARun, APackedVariableHasOneBitPerBit) {
  Run(kPackedVariables);
  EXPECT_EQ(CountOf(vpiBit, Var("top.v")), 8);
}

// §38.19: a bit is reached by its index, and holds that bit's value...
TEST_F(VariablesOfARun, TheBitAtAnIndexHoldsThatBit) {
  Run(kPackedVariables);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.v"), 3)), 1);
}

TEST_F(VariablesOfARun, TheBitBesideItHoldsItsOwn) {
  Run(kPackedVariables);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.v"), 2)), 0);
}

// ...addressed by the range the variable was declared with: index 12 of
// [15:10] is the third bit from the right.
TEST_F(VariablesOfARun, ABitIsAddressedByTheDeclaredRange) {
  Run(kPackedVariables);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.w"), 12)), 1);
}

// Detail 13: vpiIndex is the bit's index.
TEST_F(VariablesOfARun, ABitsIndexIsItsDeclaredIndex) {
  Run(kPackedVariables);
  EXPECT_EQ(IntOf(vpi_handle(vpiIndex, vpi_handle_by_index(Var("top.w"), 12))),
            12);
}

// Detail 9: a var bit's size is 1.
TEST_F(VariablesOfARun, ABitsSizeIsOne) {
  Run(kPackedVariables);
  EXPECT_EQ(vpi_get(vpiSize, vpi_handle_by_index(Var("top.v"), 3)), 1);
}

// A bit's parent is its variable.
TEST_F(VariablesOfARun, ABitsParentIsItsVariable) {
  Run(kPackedVariables);
  EXPECT_STREQ(
      vpi_get_str(vpiName,
                  vpi_handle(vpiParent, vpi_handle_by_index(Var("top.v"), 3))),
      "v");
}

// Detail 27: a var bit is an element of a packed array, whose bounds are
// static, so one whose index is a constant is a constant select.
TEST_F(VariablesOfARun, ABitAtAConstantIndexIsAConstantSelect) {
  Run(kPackedVariables);
  EXPECT_EQ(vpi_get(vpiConstantSelect, vpi_handle_by_index(Var("top.v"), 3)),
            1);
}

// Detail 27: a variable of static lifetime that no other variable holds has no
// parent, so it is a constant select.
TEST_F(VariablesOfARun, AStaticVariableWithNoParentIsAConstantSelect) {
  Run(kPackedVariables);
  EXPECT_EQ(vpi_get(vpiConstantSelect, Var("top.v")), 1);
}

// A value put to a bit is put to that bit of the variable.
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

// §37.17: a variable declared with an enum typedef is an enum var.
TEST_F(VariablesOfARun, AnEnumTypedefVariableIsAnEnumVar) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiType, Var("top.e")), vpiEnumVar);
}

// A virtual interface variable is a virtual interface var.
TEST_F(VariablesOfARun, AVirtualInterfaceVariableIsAVirtualInterfaceVar) {
  Run("interface ifc; endinterface\n"
      "module top; virtual ifc vi; endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, Var("top.vi")), vpiVirtualInterfaceVar);
}

// vpiSigned is the declaration's sign: an int is signed (§6.11)...
TEST_F(VariablesOfARun, AnIntIsSigned) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiSigned, Var("top.i")), 1);
}

// ...and a logic vector is not.
TEST_F(VariablesOfARun, ALogicVectorIsUnsigned) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiSigned, Var("top.lv")), 0);
}

// Detail 9: a string var's size is its current number of characters...
TEST_F(VariablesOfARun, AStringsSizeIsItsLength) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiSize, Var("top.s")), 5);
}

// ...an array var's the number of variables in it, fixed or current...
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

// ...and an unpacked struct's the number of its fields.
TEST_F(VariablesOfARun, AnUnpackedStructsSizeIsItsFieldCount) {
  Run(kVariableKinds);
  EXPECT_EQ(vpi_get(vpiSize, Var("top.st")), 2);
}

// Detail 20: a packed logic variable is a vector, a logic with no packed
// dimension a scalar, and an int a vector.
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

// Detail 21: an array var's vpiArrayType is the kind of array it is.
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

// §37.17: a variable declared with a struct typedef is a struct var...
TEST_F(VariablesOfARun, AStructTypedefVariableIsAStructVar) {
  Run(kAggregateTypedefs);
  EXPECT_EQ(vpi_get(vpiType, Var("top.s")), vpiStructVar);
}

// ...one declared with a union typedef a union var...
TEST_F(VariablesOfARun, AUnionTypedefVariableIsAUnionVar) {
  Run(kAggregateTypedefs);
  EXPECT_EQ(vpi_get(vpiType, Var("top.u")), vpiUnionVar);
}

// ...and the unpacked struct's size is its number of fields (detail 9).
TEST_F(VariablesOfARun, AStructTypedefVariablesSizeIsItsFieldCount) {
  Run(kAggregateTypedefs);
  EXPECT_EQ(vpi_get(vpiSize, Var("top.s")), 2);
}

constexpr const char* kPackedAggregates =
    "module top;\n"
    "  logic [1:0][3:0] m = 8'b0000_0100;\n"
    "  struct packed { logic [3:0] a; logic [3:0] b; } s = 8'h5A;\n"
    "  union packed { logic [7:0] a; bit [7:0] b; } u;\n"
    "endmodule\n";

// §37.17 detail 12: a packed array variable of two dimensions has a var bit
// per bit of its whole value...
TEST_F(VariablesOfARun, AMultidimensionalPackedArrayHasOneBitPerBit) {
  Run(kPackedAggregates);
  EXPECT_EQ(CountOf(vpiBit, Var("top.m")), 8);
}

// ...each named by its index in both dimensions, the leftmost first...
TEST_F(VariablesOfARun, AMultidimensionalPackedBitIsNamedByEveryIndex) {
  Run(kPackedAggregates);
  vpiHandle it = vpi_iterate(vpiBit, Var("top.m"));
  ASSERT_NE(it, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_scan(it)), "m[1][3]");
  vpi_free_object(it);
}

// ...and holding the bit of the value those indices select: m[0][2] is bit 2.
TEST_F(VariablesOfARun, AMultidimensionalPackedBitHoldsItsBit) {
  Run(kPackedAggregates);
  EXPECT_EQ(IntOf(Named(vpiBit, Var("top.m"), "m[0][2]")), 1);
}

TEST_F(VariablesOfARun, TheMultidimensionalPackedBitBesideItHoldsItsOwn) {
  Run(kPackedAggregates);
  EXPECT_EQ(IntOf(Named(vpiBit, Var("top.m"), "m[1][2]")), 0);
}

// Detail 13: its vpiIndex is the innermost index...
TEST_F(VariablesOfARun, AMultidimensionalPackedBitsIndexIsTheInnermost) {
  Run(kPackedAggregates);
  EXPECT_EQ(IntOf(vpi_handle(vpiIndex, Named(vpiBit, Var("top.m"), "m[0][2]"))),
            2);
}

// ...and its vpiIndex iteration reaches its indices from that one outward.
TEST_F(VariablesOfARun, AMultidimensionalPackedBitsIndicesRunOutward) {
  Run(kPackedAggregates);
  EXPECT_EQ(IntsOf(vpiIndex, Named(vpiBit, Var("top.m"), "m[0][2]")),
            (std::vector<int>{2, 0}));
}

// Detail 12: a packed struct variable has a var bit per bit, indexed by its
// implicit range [7:0]...
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

// ...and so has a packed union variable.
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

// The left bound of each range `ref`'s vpiRange iteration reaches, in order.
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

// §37.17 detail 6: a packed variable's vpiLeftRange and vpiRightRange are the
// bounds of its leftmost packed dimension...
TEST_F(VariablesOfARun, APackedVariablesLeftRangeIsItsLeftBound) {
  Run(kDimensions);
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, Var("top.v"))), 7);
}

TEST_F(VariablesOfARun, APackedVariablesRightRangeIsItsRightBound) {
  Run(kDimensions);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, Var("top.v"))), 0);
}

// ...and an array's those of its leftmost unpacked dimension.
TEST_F(VariablesOfARun, AnArraysLeftRangeIsItsLeftUnpackedBound) {
  Run(kDimensions);
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, Var("top.arr"))), 3);
}

TEST_F(VariablesOfARun, AnArraysRightRangeIsItsRightUnpackedBound) {
  Run(kDimensions);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, Var("top.arr"))), 6);
}

// Where the leftmost range is empty, as a queue's is, both are null.
TEST_F(VariablesOfARun, AQueuesLeftRangeIsNull) {
  Run(kDimensions);
  EXPECT_EQ(vpi_handle(vpiLeftRange, Var("top.q")), nullptr);
}

// Detail 4: an array's vpiRange iteration reaches a range per unpacked
// dimension, the leftmost first...
TEST_F(VariablesOfARun, AnArraysRangesAreItsUnpackedDimensions) {
  Run(kDimensions);
  EXPECT_EQ(LeftBoundsOf(Var("top.md")), (std::vector<int>{0, 0}));
}

// ...each sized by the elements its dimension holds (§37.22)...
TEST_F(VariablesOfARun, ARangesSizeIsItsElementCount) {
  Run(kDimensions);
  vpiHandle it = vpi_iterate(vpiRange, Var("top.md"));
  ASSERT_NE(it, nullptr);
  vpi_scan(it);
  EXPECT_EQ(vpi_get(vpiSize, vpi_scan(it)), 3);
  vpi_free_object(it);
}

// ...a queue's being one empty range...
TEST_F(VariablesOfARun, AQueuesRangeIsEmpty) {
  Run(kDimensions);
  EXPECT_EQ(CountOf(vpiRange, Var("top.q")), 1);
}

// ...and a packed array's a range per packed dimension.
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

// §38.19: an element of an array var is reached by its index...
TEST_F(VariablesOfARun, AnArrayElementIsReachedByIndex) {
  Run(kFixedArrays);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.arr"), 2)), 7);
}

// ...and §37.17 detail 2 makes it a member of the array...
TEST_F(VariablesOfARun, AnArrayElementIsAnArrayMember) {
  Run(kFixedArrays);
  EXPECT_EQ(vpi_get(vpiArrayMember, vpi_handle_by_index(Var("top.arr"), 2)), 1);
}

// ...whose vpiParent is the array (detail 26)...
TEST_F(VariablesOfARun, AnArrayElementsParentIsTheArray) {
  Run(kFixedArrays);
  EXPECT_STREQ(
      vpi_get_str(vpiName, vpi_handle(vpiParent,
                                      vpi_handle_by_index(Var("top.arr"), 2))),
      "arr");
}

// ...and which is still reached by its full name.
TEST_F(VariablesOfARun, AnArrayElementIsReachedByName) {
  Run(kFixedArrays);
  EXPECT_EQ(IntOf(Var("top.arr[2]")), 7);
}

// Detail 27: an element of an array whose bounds are static, at a constant
// index, is a constant select.
TEST_F(VariablesOfARun, AStaticArrayElementIsAConstantSelect) {
  Run(kFixedArrays);
  EXPECT_EQ(vpi_get(vpiConstantSelect, vpi_handle_by_index(Var("top.arr"), 2)),
            1);
}

// A multidimensional array's subarray is an array var of its own, reached by
// the outer index, whose elements the inner index reaches (§38.19)...
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

// ...and both indices together (§38.20).
TEST_F(VariablesOfARun, AnElementOfAMultidimensionalArrayIsReachedByIndices) {
  Run(kFixedArrays);
  PLI_INT32 indices[] = {1, 2};
  EXPECT_EQ(IntOf(vpi_handle_by_multi_index(Var("top.m"), 2, indices)), 9);
}

// Detail 18: an element's vpiIndex iteration reaches the indices selecting it
// out of the array, its own first.
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

// §38.19 with §37.17: an element of a queue is reached by its index...
TEST_F(VariablesOfARun, AQueueElementIsReachedByIndex) {
  Run(kVariableSizedArrays);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.q"), 1)), 5);
}

// ...as is one of a dynamic array...
TEST_F(VariablesOfARun, ADynamicArrayElementIsReachedByIndex) {
  Run(kVariableSizedArrays);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.d"), 4)), 8);
}

// ...and one of an associative array by its key.
TEST_F(VariablesOfARun, AnAssociativeArrayElementIsReachedByKey) {
  Run(kVariableSizedArrays);
  EXPECT_EQ(IntOf(vpi_handle_by_index(Var("top.aa"), 10)), 3);
}

// An index the array holds no element at reaches nothing.
TEST_F(VariablesOfARun, AnIndexPastAQueuesEndReachesNothing) {
  Run(kVariableSizedArrays);
  EXPECT_EQ(vpi_handle_by_index(Var("top.q"), 7), nullptr);
}

// The element is a member of its array (detail 2).
TEST_F(VariablesOfARun, AQueueElementIsAnArrayMember) {
  Run(kVariableSizedArrays);
  EXPECT_EQ(vpi_get(vpiArrayMember, vpi_handle_by_index(Var("top.q"), 1)), 1);
}

// Detail 27: a queue's bounds are not static, so none of its elements is a
// constant select.
TEST_F(VariablesOfARun, AQueueElementIsNoConstantSelect) {
  Run(kVariableSizedArrays);
  EXPECT_EQ(vpi_get(vpiConstantSelect, vpi_handle_by_index(Var("top.q"), 1)),
            0);
}

// A value put to the element is put into the array's store, where the next
// selection of it reads it.
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

// §37.17 detail 3 with §37.26: an unpacked struct var has a member variable
// per field...
TEST_F(VariablesOfARun, AnUnpackedStructHasAMemberPerField) {
  Run(kUnpackedStruct);
  EXPECT_EQ(NamesOf(vpiMember, Var("top.s")),
            (std::vector<std::string>{"a", "b"}));
}

// ...reached by its full name and holding the field's value...
TEST_F(VariablesOfARun, AStructMemberHoldsItsFieldsValue) {
  Run(kUnpackedStruct);
  EXPECT_EQ(IntOf(Var("top.s.b")), 6);
}

TEST_F(VariablesOfARun, TheStructMemberBesideItHoldsItsOwn) {
  Run(kUnpackedStruct);
  EXPECT_EQ(IntOf(Var("top.s.a")), 5);
}

// ...whose vpiParent is the struct var (detail 26)...
TEST_F(VariablesOfARun, AStructMembersParentIsTheStruct) {
  Run(kUnpackedStruct);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiParent, Var("top.s.b"))),
               "s");
}

// ...which is a constant select (detail 27)...
TEST_F(VariablesOfARun, AStructMemberIsAConstantSelect) {
  Run(kUnpackedStruct);
  EXPECT_EQ(vpi_get(vpiConstantSelect, Var("top.s.b")), 1);
}

// ...and its kind is the field's type (detail 17).
TEST_F(VariablesOfARun, AStructMembersKindIsItsFieldsType) {
  Run(kUnpackedStruct);
  EXPECT_EQ(vpi_get(vpiType, Var("top.s.b")), vpiIntVar);
}

// A member of a real, short real, string or enum type is the kind §37.17 draws
// for that type, as a variable of it is, whether the field names the type or a
// typedef standing for it (#5036)...
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

// ...and a real member holds its field's value as a real.
TEST_F(VariablesOfARun, ARealStructMemberHoldsARealValue) {
  Run("module top; struct {int a; real r;} m = '{1, 2.5}; endmodule\n");
  s_vpi_value value = {};
  value.format = vpiObjTypeVal;
  vpi_get_value(Var("top.m.r"), &value);
  EXPECT_EQ(value.format, vpiRealVal);
  EXPECT_DOUBLE_EQ(value.value.real, 2.5);
}

// A value put to a member is put into the struct's field, and leaves the other
// field as it was.
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

// §37.85 detail 5 with §37.25: each typedef a module declares is a typespec
// its vpiTypedef iteration reaches, named after the typedef...
TEST_F(VariablesOfARun, AModulesTypedefsAreTypespecs) {
  Run(kTypedefs);
  EXPECT_EQ(NamesOf(vpiTypedef, Var("top")),
            (std::vector<std::string>{"e_t", "s_t"}));
}

// ...an enum typedef's with its constants...
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

// ...and a struct typedef's with its members (§37.26).
TEST_F(VariablesOfARun, AStructTypespecHasItsMembers) {
  Run(kTypedefs);
  EXPECT_EQ(NamesOf(vpiTypespecMember, Named(vpiTypedef, Var("top"), "s_t")),
            (std::vector<std::string>{"a", "b"}));
}

// §37.17: a variable declared with a typedef reaches its typespec...
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

// ...and one declared with a typedef of the compilation unit, the unit's.
TEST_F(VariablesOfARun, AVariablesTypespecIsTheUnitsTypedef) {
  Run(kTypedefs);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiTypespec, Var("top.u"))),
               "ue_t");
}

// The right side of the continuous assignment that drives `target`, read off
// the instance `top`.
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

// Detail 26: a select of an outer packed dimension is a logic var vector the
// size of the element it selects, whose parent is the vector it selects
// from, holding the element its index now names (#4986)...
TEST_F(VariablesOfARun, AVaryingOuterPackedSelectIsAVectorOfItsElement) {
  Run(kPackedSelects);
  vpiHandle rhs = RhsDriving("top.y");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiLogicVar);
  EXPECT_EQ(vpi_get(vpiSize, rhs), 8);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, rhs)), VpiObjectOf(Var("top.m")));
  EXPECT_EQ(IntOf(rhs), 0x22);
}

// ...named by its index where that is a constant...
TEST_F(VariablesOfARun, AConstantOuterPackedSelectIsNamedByItsIndex) {
  Run(kPackedSelects);
  vpiHandle rhs = RhsDriving("top.z");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiLogicVar);
  EXPECT_EQ(vpi_get(vpiSize, rhs), 8);
  EXPECT_STREQ(vpi_get_str(vpiName, rhs), "m[2]");
  EXPECT_EQ(IntOf(rhs), 0x33);
}

// ...and a select indexing every packed dimension is the var bit it names.
TEST_F(VariablesOfARun, ASelectOfEveryPackedDimensionIsItsVarBit) {
  Run(kPackedSelects);
  vpiHandle rhs = RhsDriving("top.b");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiRegBit);
  EXPECT_STREQ(vpi_get_str(vpiName, rhs), "m[2][1]");
  EXPECT_EQ(IntOf(rhs), 1);
}

// §38.34: a value put to such a select lands in the bits of the vector it
// spans, those a constant index names and those a varying index names when
// the value is put (#5066).
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

// A variable a generate block declares is named as declared, under the gen
// scope of its block instance, and full-named through it (§27.4); the
// instance holds no variable of a name joining the two, and an expression
// written in the block reaches that variable, its value shared (#5068).
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

}  // namespace
}  // namespace delta
