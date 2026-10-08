#include <gtest/gtest.h>

#include <string>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&net)), vpiNet);

  VpiObject mod;
  mod.type = vpiModule;
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&mod)), vpiModule);
}

// Claim: vpi_get_str(vpiType, handle) returns a pointer to a string holding the
// name of the type constant - the identifier the type is known by in the data
// model diagram.
TEST_F(VpiObjectTypeProperty, GetStrTypeReturnsTheTypeConstantName) {
  VpiObject net;
  net.type = vpiNet;
  const char* net_name = vpi_get_str(vpiType, VpiHandleOf(&net));
  ASSERT_NE(net_name, nullptr);
  EXPECT_EQ(std::string(net_name), "vpiNet");

  VpiObject mod;
  mod.type = vpiModule;
  const char* mod_name = vpi_get_str(vpiType, VpiHandleOf(&mod));
  ASSERT_NE(mod_name, nullptr);
  EXPECT_EQ(std::string(mod_name), "vpiModule");
}

// Edge of the vpiType string rule: a value neither Annex K nor Annex M defines
// as an object type has no type constant to name, so the string accessor
// reports no name (a null pointer) rather than inventing one - the same null
// the routine yields for any property it cannot supply.
TEST_F(VpiObjectTypeProperty, GetStrTypeYieldsNoNameForAnUndefinedType) {
  VpiObject odd;
  odd.type = 9999;  // no object type of either annex
  EXPECT_EQ(vpi_get_str(vpiType, VpiHandleOf(&odd)), nullptr);
}

// The string form names every object type the annexes define, each by its
// own constant's spelling: the first and last of Annex K's list, kinds of
// Annex M's, and its last.
std::string TypeNameOf(int type) {
  VpiObject obj;
  obj.type = type;
  const char* name = vpi_get_str(vpiType, VpiHandleOf(&obj));
  return name == nullptr ? "" : name;
}

TEST_F(VpiObjectTypeProperty, GetStrTypeNamesTheFirstAnnexKType) {
  EXPECT_EQ(TypeNameOf(vpiAlways), "vpiAlways");
}

TEST_F(VpiObjectTypeProperty, GetStrTypeNamesAMemory) {
  EXPECT_EQ(TypeNameOf(vpiMemory), "vpiMemory");
}

TEST_F(VpiObjectTypeProperty, GetStrTypeNamesAnIntVar) {
  EXPECT_EQ(TypeNameOf(vpiIntVar), "vpiIntVar");
}

TEST_F(VpiObjectTypeProperty, GetStrTypeNamesAGenScope) {
  EXPECT_EQ(TypeNameOf(vpiGenScope), "vpiGenScope");
}

TEST_F(VpiObjectTypeProperty, GetStrTypeNamesAClassDefn) {
  EXPECT_EQ(TypeNameOf(vpiClassDefn), "vpiClassDefn");
}

TEST_F(VpiObjectTypeProperty, GetStrTypeNamesTheLastAnnexMType) {
  EXPECT_EQ(TypeNameOf(vpiLetExpr), "vpiLetExpr");
}

// §37.17 detail 19: a var bit may be named vpiRegBit, the spelling of the
// shared value Annex K defines.
TEST_F(VpiObjectTypeProperty, GetStrTypeNamesAVarBitByItsAnnexKSpelling) {
  EXPECT_EQ(TypeNameOf(vpiVarBit), "vpiRegBit");
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

  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&op)), vpiAddOp);
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
  EXPECT_EQ(vpi_get(vpiPrimType, VpiHandleOf(&seq)), vpiSeqPrim);

  VpiObject comb;
  comb.type = vpiPrimitive;
  comb.prim_type = vpiCombPrim;
  EXPECT_EQ(vpi_get(vpiPrimType, VpiHandleOf(&comb)), vpiCombPrim);
}

// Claim D, third input form: vpiDelayType is likewise one of the additional
// type properties. vpi_get(vpiDelayType, handle) returns the integer constant
// for the delay kind the object carries, through yet another production path.
TEST_F(VpiObjectTypeProperty, GetReturnsTheDelayTypeAdditionalProperty) {
  VpiObject mod_path;
  mod_path.type = vpiModPath;
  mod_path.delay_type = vpiModPathDelay;
  EXPECT_EQ(vpi_get(vpiDelayType, VpiHandleOf(&mod_path)), vpiModPathDelay);

  VpiObject inter_mod;
  inter_mod.type = vpiInterModPath;
  inter_mod.delay_type = vpiInterModPathDelay;
  EXPECT_EQ(vpi_get(vpiDelayType, VpiHandleOf(&inter_mod)),
            vpiInterModPathDelay);
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
  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&add)), vpiAddOp);
  const char* add_name = vpi_get_str(vpiOpType, VpiHandleOf(&add));
  ASSERT_NE(add_name, nullptr);
  EXPECT_EQ(std::string(add_name), "vpiAddOp");

  // A different operator value names its own constant, confirming the string
  // form tracks the reported integer rather than a fixed spelling.
  VpiObject shift;
  shift.type = vpiOperation;
  shift.op_type = vpiLShiftOp;
  const char* shift_name = vpi_get_str(vpiOpType, VpiHandleOf(&shift));
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

  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&op)), 0);
  EXPECT_EQ(vpi_get_str(vpiOpType, VpiHandleOf(&op)), nullptr);
}

// §37.3.2: the operator constants are Annex K's and those Annex M adds, and
// vpi_get_str(vpiOpType) names each one, from the first of all, vpiMinusOp, to
// the last, vpiInsideOp, a cast and a wildcard equality among them. The Annex
// M constants had no name.
TEST_F(VpiObjectTypeProperty, GetStrNamesTheOperatorsAnnexMAdds) {
  const struct {
    int op_type;
    const char* name;
  } kOperators[] = {{vpiMinusOp, "vpiMinusOp"},
                    {vpiCastOp, "vpiCastOp"},
                    {vpiWildEqOp, "vpiWildEqOp"},
                    {vpiStreamLROp, "vpiStreamLROp"},
                    {vpiInsideOp, "vpiInsideOp"}};
  for (const auto& op : kOperators) {
    VpiObject obj;
    obj.type = vpiOperation;
    obj.op_type = op.op_type;
    const char* name = vpi_get_str(vpiOpType, VpiHandleOf(&obj));
    ASSERT_NE(name, nullptr) << op.name;
    EXPECT_EQ(std::string(name), op.name);
  }
}

// §37.3.2: vpiPrimType, vpiDelayType and vpiTchkType are additional type
// properties too, and vpi_get_str names the constant each reports, from the
// first to the last of its set in Annex K; a value outside the set has no
// name. None of the three had a name.
TEST_F(VpiObjectTypeProperty, GetStrNamesThePrimitiveDelayAndCheckTypes) {
  VpiObject prim;
  prim.type = vpiPrimitive;
  VpiObject path;
  path.type = vpiModPath;
  VpiObject check;
  check.type = vpiTchk;
  const struct {
    VpiObject* obj;
    int property;
    int* field;
    int value;
    const char* name;
  } kCases[] = {
      {&prim, vpiPrimType, &prim.prim_type, vpiAndPrim, "vpiAndPrim"},
      {&prim, vpiPrimType, &prim.prim_type, vpiCombPrim, "vpiCombPrim"},
      {&path, vpiDelayType, &path.delay_type, vpiModPathDelay,
       "vpiModPathDelay"},
      {&path, vpiDelayType, &path.delay_type, vpiMIPDelay, "vpiMIPDelay"},
      {&check, vpiTchkType, &check.tchk_type, vpiSetup, "vpiSetup"},
      {&check, vpiTchkType, &check.tchk_type, vpiTimeskew, "vpiTimeskew"},
      {&prim, vpiPrimType, &prim.prim_type, 0, nullptr},
  };
  for (const auto& c : kCases) {
    *c.field = c.value;
    const char* name = vpi_get_str(c.property, VpiHandleOf(c.obj));
    if (c.name == nullptr) {
      EXPECT_EQ(name, nullptr);
      continue;
    }
    ASSERT_NE(name, nullptr) << c.name;
    EXPECT_EQ(std::string(name), c.name);
  }
}

}  // namespace
}  // namespace delta
