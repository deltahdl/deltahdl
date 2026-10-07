#include <gtest/gtest.h>

#include <type_traits>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.4.2 (Diagram key for accessing properties) says how a property drawn on
// an object in the data model diagrams is read back, and it does so by naming
// both the routine and the type: vpi_get() reads integer and Boolean
// properties, which are PLI_INT32, and vpi_get_str() reads string properties,
// which are PLI_BYTE8 *. Complex properties for time and logic value are left
// to the routines the diagram indicates instead.
//
// The clause writes each access out as a line of an application, which is what
// these cases run: a property is not accessible in the sense §37.4.2 means
// unless the line the clause writes compiles and answers.
class VpiPropertyAccess : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // The clause's own `obj_h`: an object carrying one property of each of the
  // three kinds - the Boolean vpiVector and the integer vpiSize, which §37.16
  // draws on a net, and the string vpiName.
  VpiObject* ObjH() {
    net_.type = kVpiNet;
    net_.size = 8;
    net_.name = "bus";
    return &net_;
  }

  VpiObject net_;
  VpiContext ctx_;
};

// Claim: vpi_get() is the routine for integer and Boolean properties. These are
// the clause's two example lines, run unchanged.
TEST_F(VpiPropertyAccess, IntegerAndBooleanPropertiesComeFromVpiGet) {
  vpiHandle obj_h = VpiHandleOf(ObjH());

  PLI_INT32 vect_flag = vpi_get(vpiVector, obj_h);
  PLI_INT32 size = vpi_get(vpiSize, obj_h);

  EXPECT_EQ(vect_flag, 1);
  EXPECT_EQ(size, 8);
}

// Claim: those properties are PLI_INT32. The value vpi_get() hands back is of
// that type, not merely of one that converts to it - an application that stores
// the result in a PLI_INT32 is copying the clause, and a routine answering in
// some other width would leave it doing a conversion the clause does not write.
TEST_F(VpiPropertyAccess, AnIntegerPropertyIsOfTypePliInt32) {
  vpiHandle obj_h = VpiHandleOf(ObjH());

  static_assert(std::is_same_v<decltype(vpi_get(vpiSize, obj_h)), PLI_INT32>);
  EXPECT_EQ(sizeof(vpi_get(vpiSize, obj_h)), sizeof(PLI_INT32));
}

// Claim: vpi_get_str() is the routine for string properties, which are
// PLI_BYTE8 *. This is the clause's third example line, and the declared type
// of the variable it assigns to is the point of it: a pointer to const cannot
// be stored in a PLI_BYTE8 *, so a routine handing one back is not answering
// with the type the clause gives a string property.
TEST_F(VpiPropertyAccess, AStringPropertyComesFromVpiGetStrAsPliByte8) {
  vpiHandle obj_h = VpiHandleOf(ObjH());

  PLI_BYTE8* name = vpi_get_str(vpiName, obj_h);

  static_assert(
      std::is_same_v<decltype(vpi_get_str(vpiName, obj_h)), PLI_BYTE8*>);
  ASSERT_NE(name, nullptr);
  EXPECT_STREQ(name, "bus");
}

// Claim: the two routines answer for the two kinds of property and are not
// interchangeable. The integer property has no string form of its own and the
// string property is not a number, so each is read through the routine
// §37.4.2 names for it.
TEST_F(VpiPropertyAccess, EachKindIsReadThroughItsOwnRoutine) {
  vpiHandle obj_h = VpiHandleOf(ObjH());

  // vpiSize is drawn `int:`, so vpi_get() is what carries its value; asking
  // vpi_get_str() for it yields no string.
  EXPECT_EQ(vpi_get(vpiSize, obj_h), 8);
  EXPECT_EQ(vpi_get_str(vpiSize, obj_h), nullptr);
}

// Claim: a time or logic value property, being complex, is read with the
// routine the diagram names for it. A logic value is one of those, and the
// routine the diagrams indicate for it is vpi_get_value(), which fills a
// caller's s_vpi_value rather than answering with a PLI_INT32.
TEST_F(VpiPropertyAccess, AComplexValuePropertyComesFromItsOwnRoutine) {
  Arena arena;
  Variable backing;
  backing.value = MakeLogic4VecVal(arena, 32, 7u);

  VpiObject var;
  var.type = kVpiReg;
  var.var = &backing;

  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(VpiHandleOf(&var), &value);

  EXPECT_EQ(value.value.integer, 7);
}

}  // namespace
}  // namespace delta
