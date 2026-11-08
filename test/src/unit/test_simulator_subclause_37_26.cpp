#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class StructuresAndUnions : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

constexpr int kStructUnionKinds[] = {vpiStructVar, vpiUnionVar, vpiStructNet,
                                     vpiUnionNet};

TEST_F(StructuresAndUnions, PackedPropertyReportsDeclaredFlag) {
  VpiObject packed_struct;
  packed_struct.type = vpiStructVar;
  packed_struct.packed = true;
  EXPECT_EQ(vpi_get(vpiPacked, VpiHandleOf(&packed_struct)), 1);

  VpiObject unpacked_struct;
  unpacked_struct.type = vpiStructVar;
  EXPECT_EQ(vpi_get(vpiPacked, VpiHandleOf(&unpacked_struct)), 0);
}

TEST_F(StructuresAndUnions, TaggedPropertyReportsDeclaredFlag) {
  VpiObject tagged_union;
  tagged_union.type = vpiUnionVar;
  tagged_union.tagged = true;
  EXPECT_EQ(vpi_get(vpiTagged, VpiHandleOf(&tagged_union)), 1);

  VpiObject plain_union;
  plain_union.type = vpiUnionVar;
  EXPECT_EQ(vpi_get(vpiTagged, VpiHandleOf(&plain_union)), 0);
}

TEST_F(StructuresAndUnions, SoftPropertyReportsDeclaredFlag) {
  VpiObject soft_union;
  soft_union.type = vpiUnionVar;
  soft_union.packed = true;
  soft_union.soft = true;
  EXPECT_EQ(vpi_get(vpiSoft, VpiHandleOf(&soft_union)), 1);

  VpiObject hard_union;
  hard_union.type = vpiUnionVar;
  hard_union.packed = true;
  EXPECT_EQ(vpi_get(vpiSoft, VpiHandleOf(&hard_union)), 0);
}

TEST_F(StructuresAndUnions, GetValueRejectsEntireUnpackedStructOrUnion) {
  for (int kind : kStructUnionKinds) {
    VpiObject aggregate;
    aggregate.type = kind;

    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = 0x5eed;

    vpi_get_value(VpiHandleOf(&aggregate), &value);

    s_vpi_error_info info = {};
    EXPECT_EQ(vpi_chk_error(&info), vpiError) << "kind " << kind;
    EXPECT_EQ(value.value.integer, 0x5eed) << "kind " << kind;
  }
}

TEST_F(StructuresAndUnions, PutValueRejectsEntireUnpackedStructOrUnion) {
  for (int kind : kStructUnionKinds) {
    VpiObject aggregate;
    aggregate.type = kind;

    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = 1;

    vpiHandle ret =
        vpi_put_value(VpiHandleOf(&aggregate), &value, nullptr, vpiNoDelay);
    EXPECT_EQ(ret, nullptr) << "kind " << kind;

    s_vpi_error_info info = {};
    EXPECT_EQ(vpi_chk_error(&info), vpiError) << "kind " << kind;
  }
}

TEST_F(StructuresAndUnions, PackedStructOrUnionValueIsNotRefused) {
  for (int kind : kStructUnionKinds) {
    VpiObject aggregate;
    aggregate.type = kind;
    aggregate.packed = true;

    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = 0;

    vpi_get_value(VpiHandleOf(&aggregate), &value);
    s_vpi_error_info get_info = {};
    EXPECT_EQ(vpi_chk_error(&get_info), 0) << "get, kind " << kind;

    vpi_put_value(VpiHandleOf(&aggregate), &value, nullptr, vpiNoDelay);
    s_vpi_error_info put_info = {};
    EXPECT_EQ(vpi_chk_error(&put_info), 0) << "put, kind " << kind;
  }
}

TEST_F(StructuresAndUnions, RestrictionDoesNotApplyToOrdinaryObjects) {
  for (int kind : {vpiReg, vpiNet}) {
    VpiObject obj;
    obj.type = kind;

    s_vpi_value value = {};
    value.format = vpiIntVal;

    vpi_get_value(VpiHandleOf(&obj), &value);
    s_vpi_error_info get_info = {};
    EXPECT_EQ(vpi_chk_error(&get_info), 0) << "get, kind " << kind;

    vpi_put_value(VpiHandleOf(&obj), &value, nullptr, vpiNoDelay);
    s_vpi_error_info put_info = {};
    EXPECT_EQ(vpi_chk_error(&put_info), 0) << "put, kind " << kind;
  }
}

TEST_F(StructuresAndUnions, AStructVariableReachesTheVariablesItHolds) {
  VpiObject aggregate;
  aggregate.type = vpiStructVar;

  VpiObject first;
  first.type = vpiLogicVar;
  first.parent = &aggregate;
  VpiObject second;
  second.type = vpiIntVar;
  second.parent = &aggregate;
  VpiObject typespec;
  typespec.type = vpiStructTypespec;
  typespec.parent = &aggregate;
  aggregate.children = {&first, &typespec, &second};

  vpiHandle it = vpi_iterate(vpiMember, VpiHandleOf(&aggregate));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &first);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &second);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(StructuresAndUnions, AUnionVariableReachesItsMembers) {
  VpiObject aggregate;
  aggregate.type = vpiUnionVar;

  VpiObject nested;
  nested.type = vpiStructVar;
  nested.parent = &aggregate;
  aggregate.children = {&nested};

  vpiHandle it = vpi_iterate(vpiMember, VpiHandleOf(&aggregate));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &nested);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(StructuresAndUnions, AStructNetReachesTheNetsItHolds) {
  VpiObject aggregate;
  aggregate.type = vpiStructNet;

  VpiObject member;
  member.type = kVpiNet;
  member.parent = &aggregate;
  aggregate.children = {&member};

  vpiHandle it = vpi_iterate(vpiMember, VpiHandleOf(&aggregate));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &member);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(StructuresAndUnions, AnAggregateWithNoMembersReachesNone) {
  VpiObject empty;
  empty.type = vpiStructVar;
  EXPECT_EQ(vpi_iterate(vpiMember, VpiHandleOf(&empty)), nullptr);

  VpiObject plain;
  plain.type = vpiLogicVar;
  VpiObject child;
  child.type = vpiLogicVar;
  child.parent = &plain;
  plain.children = {&child};
  EXPECT_EQ(vpi_iterate(vpiMember, VpiHandleOf(&plain)), nullptr);
}

class StructuresOfARun : public VpiDesignRun {
 protected:
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }
};

TEST_F(StructuresOfARun, APackedStructVarHasAMemberPerField) {
  Run("module top; struct packed {logic a; logic [1:0] b;} s = 3'b110;\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiMember, By("top.s")),
            (std::vector<std::string>{"a", "b"}));
  vpiHandle b = By("top.s.b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, b), 2);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, b)), VpiObjectOf(By("top.s")));
  EXPECT_EQ(IntOf(b), 2);
  EXPECT_EQ(IntOf(By("top.s.a")), 1);
}

TEST_F(StructuresOfARun, AStructOrUnionNetHasItsOwnKind) {
  Run("module top;\n"
      "  typedef struct packed {logic a; logic b;} pair_t;\n"
      "  typedef union packed {logic [1:0] x; logic [1:0] y;} both_t;\n"
      "  wire pair_t n;\n"
      "  wire both_t u;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.n")), vpiStructNet);
  EXPECT_EQ(vpi_get(vpiType, By("top.u")), vpiUnionNet);
}

TEST_F(StructuresOfARun, AStructNetHasAMemberNetPerField) {
  Run("module top;\n"
      "  typedef struct packed {logic a; logic b;} pair_t;\n"
      "  wire pair_t n;\n"
      "  assign n = 2'b10;\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiMember, By("top.n")),
            (std::vector<std::string>{"a", "b"}));
  vpiHandle a = By("top.n.a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, a)), VpiObjectOf(By("top.n")));
  EXPECT_EQ(IntOf(a), 1);
  EXPECT_EQ(IntOf(By("top.n.b")), 0);
}

TEST(StructuresAndUnionsModel, OnlyChildrenOfTheMemberKindAreMembers) {
  EXPECT_TRUE(VpiStructUnionMembers(nullptr).empty());
  VpiObject other;
  other.type = vpiStructVar;
  VpiObject var;
  var.type = vpiStructVar;
  VpiObject adopted;
  adopted.type = vpiIntVar;
  adopted.parent = &other;
  VpiObject typespec;
  typespec.type = vpiStructTypespec;
  typespec.parent = &var;
  var.children = {&adopted, &typespec};
  EXPECT_TRUE(VpiStructUnionMembers(&var).empty());
  VpiObject net;
  net.type = vpiStructNet;
  VpiObject bit;
  bit.type = vpiNetBit;
  bit.parent = &net;
  VpiObject net_typespec;
  net_typespec.type = vpiStructTypespec;
  net_typespec.parent = &net;
  net.children = {&bit, &net_typespec};
  EXPECT_TRUE(VpiStructUnionMembers(&net).empty());
}

class UnionFlagsOfARun : public VpiDesignRun {};

TEST_F(UnionFlagsOfARun, AUnionReportsWhetherItIsTaggedOrSoft) {
  Run("module top;\n"
      "  typedef union tagged { int a; bit b; } tu_t;\n"
      "  tu_t t;\n"
      "  union soft packed { logic [3:0] a; logic [1:0] b; } s;\n"
      "  union packed { logic [3:0] a; logic [3:0] b; } p;\n"
      "  wire union soft packed { logic [3:0] a; logic [1:0] b; } ws;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiTagged, By("top.t")), 1);
  EXPECT_EQ(vpi_get(vpiSoft, By("top.t")), 0);
  EXPECT_EQ(vpi_get(vpiSoft, By("top.s")), 1);
  EXPECT_EQ(vpi_get(vpiTagged, By("top.s")), 0);
  EXPECT_EQ(vpi_get(vpiTagged, By("top.p")), 0);
  EXPECT_EQ(vpi_get(vpiSoft, By("top.p")), 0);
  EXPECT_EQ(vpi_get(vpiType, By("top.ws")), vpiUnionNet);
  EXPECT_EQ(vpi_get(vpiSoft, By("top.ws")), 1);
}

}  // namespace
}  // namespace delta
