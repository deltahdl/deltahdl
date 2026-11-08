#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <type_traits>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiObjectAccess : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

TEST_F(VpiObjectAccess, GetDerivesIntegerPropertiesAsPliInt32) {
  static_assert(std::is_same_v<decltype(vpi_get(0, nullptr)), int>,
                "vpi_get must return the integer property type");
  static_assert(std::is_same_v<PLI_INT32, std::int32_t>,
                "integer/Boolean properties are PLI_INT32");

  VpiObject net;
  net.type = vpiNet;
  net.size = 8;

  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&net)), 8);
}

TEST_F(VpiObjectAccess, Get64DerivesSixtyFourBitPropertiesAsPliInt64) {
  static_assert(std::is_same_v<decltype(vpi_get64(0, nullptr)), PLI_INT64>,
                "vpi_get64 must return the 64-bit property type");
  static_assert(std::is_same_v<PLI_INT64, std::int64_t>,
                "64-bit properties are PLI_INT64");

  VpiObject obj;
  obj.type = vpiClassObj;
  obj.obj_id = (std::int64_t{1} << 32) | 7;

  EXPECT_EQ(vpi_get64(vpiObjId, VpiHandleOf(&obj)),
            (std::int64_t{1} << 32) | 7);
  EXPECT_EQ(vpi_get(vpiObjId, VpiHandleOf(&obj)), 7);
}

TEST_F(VpiObjectAccess, GetStrAccessesStringPropertiesAsPliByte8) {
  static_assert(std::is_same_v<PLI_BYTE8, char>,
                "string properties are PLI_BYTE8 *");

  VpiObject mod;
  mod.type = vpiModule;
  mod.name = "m1";
  mod.full_name = "top.m1";

  const char* full_name = vpi_get_str(vpiFullName, VpiHandleOf(&mod));
  ASSERT_NE(full_name, nullptr);
  EXPECT_EQ(std::string(full_name), "top.m1");
}

TEST_F(VpiObjectAccess, HandleTraversesOneToOneRelationship) {
  static_assert(std::is_same_v<decltype(vpi_handle(0, nullptr)), vpiHandle>,
                "vpi_handle returns a vpiHandle");

  VpiObject mod;
  mod.type = vpiModule;
  mod.name = "m1";

  VpiObject net;
  net.type = vpiNet;
  net.parent = &mod;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, VpiHandleOf(&net))), &mod);
}

TEST_F(VpiObjectAccess, IterateAndScanTraverseOneToManyRelationship) {
  VpiObject mod;
  mod.type = vpiModule;

  VpiObject w1;
  w1.type = vpiNet;
  w1.name = "w1";
  VpiObject w2;
  w2.type = vpiNet;
  w2.name = "w2";
  mod.children.push_back(&w1);
  mod.children.push_back(&w2);

  vpiHandle iter = vpi_iterate(vpiNet, VpiHandleOf(&mod));
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(vpi_get(vpiType, iter), vpiIterator);

  EXPECT_EQ(VpiObjectOf(vpi_scan(iter)), &w1);
  EXPECT_EQ(VpiObjectOf(vpi_scan(iter)), &w2);
  EXPECT_EQ(vpi_scan(iter), nullptr);
}

TEST_F(VpiObjectAccess, GetEncodesEveryBooleanPropertyAsOneOrZero) {
  VpiObject vectored_net;
  vectored_net.type = vpiNet;
  vectored_net.is_vectored = true;
  EXPECT_EQ(vpi_get(vpiExpanded, VpiHandleOf(&vectored_net)), 0);

  VpiObject plain_net;
  plain_net.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiExpanded, VpiHandleOf(&plain_net)), 1);

  VpiObject scalared_net;
  scalared_net.type = vpiNet;
  scalared_net.is_scalared = true;
  EXPECT_EQ(vpi_get(vpiExplicitScalared, VpiHandleOf(&scalared_net)), 1);
  EXPECT_EQ(vpi_get(vpiExplicitScalared, VpiHandleOf(&plain_net)), 0);
}

TEST_F(VpiObjectAccess, GetStrAccessesNamePropertyAndFullNameFallback) {
  VpiObject net;
  net.type = vpiNet;
  net.name = "w1";

  const char* name = vpi_get_str(vpiName, VpiHandleOf(&net));
  ASSERT_NE(name, nullptr);
  EXPECT_EQ(std::string(name), "w1");

  const char* full_name = vpi_get_str(vpiFullName, VpiHandleOf(&net));
  ASSERT_NE(full_name, nullptr);
  EXPECT_EQ(std::string(full_name), "w1");
}

TEST_F(VpiObjectAccess, HandleReturnsNoHandleForAbsentRelationship) {
  VpiObject net;
  net.type = vpiNet;

  EXPECT_EQ(vpi_handle(vpiModule, VpiHandleOf(&net)), nullptr);
}

}  // namespace
}  // namespace delta
