#include <gtest/gtest.h>

#include <string>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.3.2 (Object type properties) states that every object carries a vpiType
// property that is not drawn in the data model diagrams: vpi_get(vpiType, ...)
// returns the integer constant for the object's type, and vpi_get_str(vpiType,
// ...) returns the spelling of that type constant (a name derived, per §37.3,
// from the object name in the diagram). The clause also notes that some objects
// expose extra type properties shown in the diagrams (e.g. vpiOpType), reached
// the same way through vpi_get. These tests drive the production routines
// through the public C entry points, exactly as a PLI program would, by
// installing a private context as the global one.
class VpiObjectTypeProperty : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

// Claim: all objects have a vpiType property, and vpi_get(vpiType, handle)
// returns the integer constant that represents the object's type.
TEST_F(VpiObjectTypeProperty, GetTypeReturnsTheObjectTypeConstant) {
  VpiObject net;
  net.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiType, &net), vpiNet);

  VpiObject mod;
  mod.type = vpiModule;
  EXPECT_EQ(vpi_get(vpiType, &mod), vpiModule);
}

// Claim: vpi_get_str(vpiType, handle) returns a pointer to a string holding the
// name of the type constant - the identifier the type is known by in the data
// model diagram.
TEST_F(VpiObjectTypeProperty, GetStrTypeReturnsTheTypeConstantName) {
  VpiObject net;
  net.type = vpiNet;
  const char* net_name = vpi_get_str(vpiType, &net);
  ASSERT_NE(net_name, nullptr);
  EXPECT_EQ(std::string(net_name), "vpiNet");

  VpiObject mod;
  mod.type = vpiModule;
  const char* mod_name = vpi_get_str(vpiType, &mod);
  ASSERT_NE(mod_name, nullptr);
  EXPECT_EQ(std::string(mod_name), "vpiModule");
}

// Edge of the vpiType string rule: vpi_get_str names the type only for the
// object kinds the simulator actually models. For a handle whose type code the
// model does not yet carry a spelling for, the string accessor reports no name
// (a null pointer) rather than inventing one - the same null the routine yields
// for any property it cannot supply.
TEST_F(VpiObjectTypeProperty, GetStrTypeYieldsNoNameForUnmodelledType) {
  VpiObject mem;
  mem.type =
      vpiMemory;  // a valid object type, but one with no modelled spelling

  // The integer type is still reported faithfully...
  EXPECT_EQ(vpi_get(vpiType, &mem), vpiMemory);
  // ...while the string form has no name to hand back.
  EXPECT_EQ(vpi_get_str(vpiType, &mem), nullptr);
}

// Claim: some objects expose additional type properties shown in the data model
// diagrams (vpiOpType among those the clause lists), and
// vpi_get(<type_property>, handle) likewise returns an integer constant
// representing that extra type. An operation reports its operator kind through
// vpiOpType.
TEST_F(VpiObjectTypeProperty, GetReturnsAnAdditionalTypePropertyConstant) {
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiAddOp;

  EXPECT_EQ(vpi_get(vpiOpType, &op), vpiAddOp);
}

// Claim D, second input form: vpiPrimType is another of the additional type
// properties the clause names. vpi_get(vpiPrimType, handle) returns the integer
// constant for the primitive kind the object carries, reached through a
// distinct production path from vpiOpType. The value tracks the stored kind, so
// a sequential primitive and a combinational one report their own constants.
TEST_F(VpiObjectTypeProperty, GetReturnsThePrimTypeAdditionalProperty) {
  VpiObject seq;
  seq.type = vpiPrimitive;
  seq.prim_type = vpiSeqPrim;
  EXPECT_EQ(vpi_get(vpiPrimType, &seq), vpiSeqPrim);

  VpiObject comb;
  comb.type = vpiPrimitive;
  comb.prim_type = vpiCombPrim;
  EXPECT_EQ(vpi_get(vpiPrimType, &comb), vpiCombPrim);
}

// Claim D, third input form: vpiDelayType is likewise one of the additional
// type properties. vpi_get(vpiDelayType, handle) returns the integer constant
// for the delay kind the object carries, through yet another production path.
TEST_F(VpiObjectTypeProperty, GetReturnsTheDelayTypeAdditionalProperty) {
  VpiObject mod_path;
  mod_path.type = vpiModPath;
  mod_path.delay_type = vpiModPathDelay;
  EXPECT_EQ(vpi_get(vpiDelayType, &mod_path), vpiModPathDelay);

  VpiObject inter_mod;
  inter_mod.type = vpiInterModPath;
  inter_mod.delay_type = vpiInterModPathDelay;
  EXPECT_EQ(vpi_get(vpiDelayType, &inter_mod), vpiInterModPathDelay);
}

// Claim: the constant names of the types returned for the additional type
// properties can be accessed using vpi_get_str(). Alongside the integer form,
// vpi_get_str(vpiOpType, handle) hands back the spelling of the operator
// constant the operation reports - the name of the very value vpi_get()
// returns, so the two forms stay in step.
TEST_F(VpiObjectTypeProperty, GetStrReturnsAnAdditionalTypePropertyName) {
  VpiObject add;
  add.type = vpiOperation;
  add.op_type = vpiAddOp;
  EXPECT_EQ(vpi_get(vpiOpType, &add), vpiAddOp);
  const char* add_name = vpi_get_str(vpiOpType, &add);
  ASSERT_NE(add_name, nullptr);
  EXPECT_EQ(std::string(add_name), "vpiAddOp");

  // A different operator value names its own constant, confirming the string
  // form tracks the reported integer rather than a fixed spelling.
  VpiObject shift;
  shift.type = vpiOperation;
  shift.op_type = vpiLShiftOp;
  const char* shift_name = vpi_get_str(vpiOpType, &shift);
  ASSERT_NE(shift_name, nullptr);
  EXPECT_EQ(std::string(shift_name), "vpiLShiftOp");
}

// Edge of the additional-type-property string rule: vpi_get_str names the type
// only for the values the simulator models. An operation whose op-type value
// falls outside the modelled operator set still reports its integer faithfully,
// while the string accessor has no constant name to hand back (null) rather
// than inventing one.
TEST_F(VpiObjectTypeProperty,
       GetStrAdditionalTypeYieldsNoNameForUnmodelledValue) {
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = 0;  // no operator constant carries value 0

  EXPECT_EQ(vpi_get(vpiOpType, &op), 0);
  EXPECT_EQ(vpi_get_str(vpiOpType, &op), nullptr);
}

}  // namespace
}  // namespace delta
