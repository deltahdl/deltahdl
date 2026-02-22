// §41

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulation/dpi_runtime.h"

using namespace delta;

namespace {

// =============================================================================
// S41: Data Read API
// =============================================================================
TEST(Api, DataReadGetPutValue) {
  DataReadApi api;
  DataReadValue val;
  val.format = DataReadFormat::kInt;
  val.int_val = 42;
  api.StoreVariable("x", val);

  auto result = api.GetValue("x", DataReadFormat::kInt);
  EXPECT_EQ(result.int_val, 42);
  EXPECT_EQ(result.format, DataReadFormat::kInt);
}

TEST(Api, DataReadPutValueOverwrites) {
  DataReadApi api;
  DataReadValue v1;
  v1.format = DataReadFormat::kInt;
  v1.int_val = 10;
  api.StoreVariable("sig", v1);

  DataReadValue v2;
  v2.format = DataReadFormat::kInt;
  v2.int_val = 99;
  api.PutValue("sig", v2);

  auto result = api.GetValue("sig", DataReadFormat::kInt);
  EXPECT_EQ(result.int_val, 99);
}

TEST(Api, DataReadRealFormat) {
  DataReadApi api;
  DataReadValue val;
  val.format = DataReadFormat::kReal;
  val.real_val = 3.14;
  api.StoreVariable("r", val);

  auto result = api.GetValue("r", DataReadFormat::kReal);
  EXPECT_DOUBLE_EQ(result.real_val, 3.14);
}

TEST(Api, DataReadStringFormat) {
  DataReadApi api;
  DataReadValue val;
  val.format = DataReadFormat::kString;
  val.str_val = "hello_sv";
  api.StoreVariable("s", val);

  auto result = api.GetValue("s", DataReadFormat::kString);
  EXPECT_EQ(result.str_val, "hello_sv");
}

TEST(Api, DataReadVectorFormat) {
  DataReadApi api;
  DataReadValue val;
  val.format = DataReadFormat::kVector;
  val.vector_val = {{0xDEADBEEF, 0}, {0xCAFEBABE, 0}};
  api.StoreVariable("vec", val);

  auto result = api.GetValue("vec", DataReadFormat::kVector);
  ASSERT_EQ(result.vector_val.size(), 2u);
  EXPECT_EQ(result.vector_val[0].aval, 0xDEADBEEFu);
  EXPECT_EQ(result.vector_val[1].aval, 0xCAFEBABEu);
}

TEST(Api, DataReadValueChangeCallback) {
  DataReadApi api;
  DataReadValue init;
  init.format = DataReadFormat::kInt;
  init.int_val = 0;
  api.StoreVariable("sig", init);

  bool cb_fired = false;
  int cb_new_val = 0;
  api.RegisterValueChangeCb("sig",
                            [&cb_fired, &cb_new_val](std::string_view /*name*/,
                                                     const DataReadValue &val) {
                              cb_fired = true;
                              cb_new_val = val.int_val;
                            });
  EXPECT_EQ(api.ValueChangeCbCount(), 1u);

  DataReadValue updated;
  updated.format = DataReadFormat::kInt;
  updated.int_val = 42;
  api.PutValue("sig", updated);

  EXPECT_TRUE(cb_fired);
  EXPECT_EQ(cb_new_val, 42);
}

TEST(Api, DataReadMissingVariableReturnsDefault) {
  DataReadApi api;
  auto result = api.GetValue("nonexistent", DataReadFormat::kInt);
  EXPECT_EQ(result.int_val, 0);
  EXPECT_EQ(result.format, DataReadFormat::kInt);
}

}  // namespace
