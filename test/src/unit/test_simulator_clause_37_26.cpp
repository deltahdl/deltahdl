#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.26 Structures and unions: the VPI object model for a structure or union
// declared as a variable (struct/union var) or as a net (struct/union net). The
// figure's structural relations (vpiParent to the enclosing object, vpiMember
// to the member variables/nets) are served by the generic object-model
// machinery, so the tests below observe the two rules this clause's own text
// defines:
//   - The figure's Boolean properties vpiPacked, vpiTagged, and vpiSoft, read
//     through the vpi_get dispatch.
//   - Detail 1: vpi_get_value()/vpi_put_value() cannot access the value of an
//     entire unpacked structure or union, observed through the value routines.

// The fixture installs a context so the public vpi_get/vpi_get_value/
// vpi_put_value entry points run their real dispatch and so vpi_chk_error()
// reports the error the value routines record.
class StructuresAndUnions : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// The four object kinds the figure models - a struct/union declared as a
// variable and a struct/union declared as a net.
constexpr int kStructUnionKinds[] = {vpiStructVar, vpiUnionVar, vpiStructNet,
                                     vpiUnionNet};

// Figure: a struct/union object reports whether it is packed through the
// vpiPacked Boolean property. A packed aggregate reports TRUE; one left
// unpacked reports FALSE.
TEST_F(StructuresAndUnions, PackedPropertyReportsDeclaredFlag) {
  VpiObject packed_struct;
  packed_struct.type = vpiStructVar;
  packed_struct.packed = true;
  EXPECT_EQ(vpi_get(vpiPacked, &packed_struct), 1);

  VpiObject unpacked_struct;
  unpacked_struct.type = vpiStructVar;  // packed defaults false
  EXPECT_EQ(vpi_get(vpiPacked, &unpacked_struct), 0);
}

// Figure: a union object reports whether it is a tagged union through the
// vpiTagged Boolean property.
TEST_F(StructuresAndUnions, TaggedPropertyReportsDeclaredFlag) {
  VpiObject tagged_union;
  tagged_union.type = vpiUnionVar;
  tagged_union.tagged = true;
  EXPECT_EQ(vpi_get(vpiTagged, &tagged_union), 1);

  VpiObject plain_union;
  plain_union.type = vpiUnionVar;
  EXPECT_EQ(vpi_get(vpiTagged, &plain_union), 0);
}

// Figure: a packed union reports whether it is a soft-packed union through the
// vpiSoft Boolean property.
TEST_F(StructuresAndUnions, SoftPropertyReportsDeclaredFlag) {
  VpiObject soft_union;
  soft_union.type = vpiUnionVar;
  soft_union.packed = true;
  soft_union.soft = true;
  EXPECT_EQ(vpi_get(vpiSoft, &soft_union), 1);

  VpiObject hard_union;
  hard_union.type = vpiUnionVar;
  hard_union.packed = true;
  EXPECT_EQ(vpi_get(vpiSoft, &hard_union), 0);
}

// D1: vpi_get_value() cannot read the value of an entire unpacked structure or
// union. The read is refused for every struct/union object kind that is not
// packed: an error is recorded and the caller's value buffer is left untouched.
TEST_F(StructuresAndUnions, GetValueRejectsEntireUnpackedStructOrUnion) {
  for (int kind : kStructUnionKinds) {
    VpiObject aggregate;
    aggregate.type = kind;  // unpacked (packed defaults false)

    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = 0x5eed;  // sentinel the routine must not overwrite

    vpi_get_value(&aggregate, &value);

    SVpiErrorInfo info = {};
    EXPECT_EQ(VpiChkErrorC(&info), vpiError) << "kind " << kind;
    EXPECT_EQ(value.value.integer, 0x5eed) << "kind " << kind;
  }
}

// D1: vpi_put_value() likewise cannot write the value of an entire unpacked
// structure or union. The put is rejected for every unpacked struct/union kind:
// it returns NULL and records an error.
TEST_F(StructuresAndUnions, PutValueRejectsEntireUnpackedStructOrUnion) {
  for (int kind : kStructUnionKinds) {
    VpiObject aggregate;
    aggregate.type = kind;  // unpacked

    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = 1;

    vpiHandle ret = vpi_put_value(&aggregate, &value, nullptr, vpiNoDelay);
    EXPECT_EQ(ret, nullptr) << "kind " << kind;

    SVpiErrorInfo info = {};
    EXPECT_EQ(VpiChkErrorC(&info), vpiError) << "kind " << kind;
  }
}

// D1: the restriction is on the *unpacked* aggregate only. A packed structure
// or union has a single vector value, so neither value routine refuses it - the
// §37.26 guard each carries is bypassed and no error is recorded. Both routines
// carry an independent guard, so both are checked.
TEST_F(StructuresAndUnions, PackedStructOrUnionValueIsNotRefused) {
  for (int kind : kStructUnionKinds) {
    VpiObject aggregate;
    aggregate.type = kind;
    aggregate.packed = true;

    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = 0;

    vpi_get_value(&aggregate, &value);
    SVpiErrorInfo get_info = {};
    EXPECT_EQ(VpiChkErrorC(&get_info), 0) << "get, kind " << kind;

    vpi_put_value(&aggregate, &value, nullptr, vpiNoDelay);
    SVpiErrorInfo put_info = {};
    EXPECT_EQ(VpiChkErrorC(&put_info), 0) << "put, kind " << kind;
  }
}

// D1 scope: the restriction names structures and unions specifically. An
// ordinary scalar object - a reg or a net - is not a struct/union aggregate, so
// neither value routine refuses it on §37.26's account. Both routines carry an
// independent guard whose type-membership arm must let an ordinary object pass.
TEST_F(StructuresAndUnions, RestrictionDoesNotApplyToOrdinaryObjects) {
  for (int kind : {vpiReg, vpiNet}) {
    VpiObject obj;
    obj.type = kind;

    s_vpi_value value = {};
    value.format = vpiIntVal;

    vpi_get_value(&obj, &value);
    SVpiErrorInfo get_info = {};
    EXPECT_EQ(VpiChkErrorC(&get_info), 0) << "get, kind " << kind;

    vpi_put_value(&obj, &value, nullptr, vpiNoDelay);
    SVpiErrorInfo put_info = {};
    EXPECT_EQ(VpiChkErrorC(&put_info), 0) << "put, kind " << kind;
  }
}

}  // namespace
}  // namespace delta
