#include <gtest/gtest.h>

#include <cstring>
#include <string>

#include "helpers_vpi_save_restore_probe.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct SingleWrite {
  int id = 0;
  const char* data = nullptr;
  int len = 0;
  int returned = -1;
};

int WriteOnceCb(s_cb_data* cb) {
  auto* p = reinterpret_cast<SingleWrite*>(cb->user_data);
  p->returned = vpi_put_data(p->id, const_cast<char*>(p->data), p->len);
  return 0;
}

int WriteFromNullCb(s_cb_data* cb) {
  auto* p = reinterpret_cast<SingleWrite*>(cb->user_data);
  p->returned = vpi_put_data(p->id, nullptr, p->len);
  return 0;
}

struct MultiWrite {
  int id_a = 0;
  int id_b = 0;
  const char* a1 = nullptr;
  int a1_len = 0;
  const char* b = nullptr;
  int b_len = 0;
  const char* a2 = nullptr;
  int a2_len = 0;
  int ret_a1 = -1;
  int ret_b = -1;
  int ret_a2 = -1;
};

int WriteInterleavedCb(s_cb_data* cb) {
  auto* p = reinterpret_cast<MultiWrite*>(cb->user_data);
  p->ret_a1 = vpi_put_data(p->id_a, const_cast<char*>(p->a1), p->a1_len);
  p->ret_b = vpi_put_data(p->id_b, const_cast<char*>(p->b), p->b_len);
  p->ret_a2 = vpi_put_data(p->id_a, const_cast<char*>(p->a2), p->a2_len);
  return 0;
}

struct DoubleWrite {
  int id = 0;
  const char* first = nullptr;
  int first_len = 0;
  const char* second = nullptr;
  int second_len = 0;
  int ret1 = -1;
  int ret2 = -1;
};

int WriteTwiceCb(s_cb_data* cb) {
  auto* p = reinterpret_cast<DoubleWrite*>(cb->user_data);
  p->ret1 = vpi_put_data(p->id, const_cast<char*>(p->first), p->first_len);
  p->ret2 = vpi_put_data(p->id, const_cast<char*>(p->second), p->second_len);
  return 0;
}

using VpiPutDataSim = VpiSaveRestoreSim;

TEST_F(VpiPutDataSim, WritesDataInsideStartOfSave) {
  const char kPayload[] = {'D', 'e', 'l', 't', 'a'};
  SingleWrite w;
  w.id = 42;
  w.data = kPayload;
  w.len = 5;
  DispatchWith(cbStartOfSave, WriteOnceCb, &w);

  EXPECT_EQ(w.returned, 5);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);

  SingleRead r;
  r.id = 42;
  r.request = 5;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &r);
  EXPECT_EQ(r.returned, 5);
  EXPECT_EQ(0, std::memcmp(r.buf, kPayload, 5));
}

TEST_F(VpiPutDataSim, WritesDataInsideEndOfSave) {
  const char kPayload[] = {'X', 'Y', 'Z'};
  SingleWrite w;
  w.id = 7;
  w.data = kPayload;
  w.len = 3;
  DispatchWith(cbEndOfSave, WriteOnceCb, &w);

  EXPECT_EQ(w.returned, 3);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

TEST_F(VpiPutDataSim, RejectedOutsideSaveCallback) {
  const char kPayload[] = {'a', 'b', 'c', 'd'};
  int returned = vpi_put_data(1, const_cast<char*>(kPayload), 4);

  EXPECT_EQ(returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);

  SingleRead r;
  r.id = 1;
  r.request = 4;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &r);
  EXPECT_EQ(r.returned, 0);
}

TEST_F(VpiPutDataSim, RejectedInsideNonSaveCallback) {
  const char kPayload[] = {'w', 'x', 'y', 'z'};
  SingleWrite w;
  w.id = 21;
  w.data = kPayload;
  w.len = 4;
  DispatchWith(cbStartOfRestart, WriteOnceCb, &w);

  EXPECT_EQ(w.returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);

  SingleRead r;
  r.id = 21;
  r.request = 4;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &r);
  EXPECT_EQ(r.returned, 0);
}

TEST_F(VpiPutDataSim, NonPositiveCountReturnsZero) {
  const char kPayload[] = {'q'};
  SingleWrite w;
  w.id = 5;
  w.data = kPayload;
  w.len = 0;
  DispatchWith(cbStartOfSave, WriteOnceCb, &w);

  EXPECT_EQ(w.returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

TEST_F(VpiPutDataSim, NullSourceReturnsZero) {
  SingleWrite w;
  w.id = 8;
  w.len = 4;
  DispatchWith(cbStartOfSave, WriteFromNullCb, &w);

  EXPECT_EQ(w.returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

TEST_F(VpiPutDataSim, RepeatedAndInterleavedWritesAreUnrestricted) {
  const char kA1[] = {'0', '1'};
  const char kB[] = {'!', '?'};
  const char kA2[] = {'2', '3', '4'};
  MultiWrite w;
  w.id_a = 9;
  w.id_b = 10;
  w.a1 = kA1;
  w.a1_len = 2;
  w.b = kB;
  w.b_len = 2;
  w.a2 = kA2;
  w.a2_len = 3;
  DispatchWith(cbStartOfSave, WriteInterleavedCb, &w);

  EXPECT_EQ(w.ret_a1, 2);
  EXPECT_EQ(w.ret_b, 2);
  EXPECT_EQ(w.ret_a2, 3);

  SingleRead ra;
  ra.id = 9;
  ra.request = 5;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &ra);
  EXPECT_EQ(ra.returned, 5);
  EXPECT_EQ(0, std::memcmp(ra.buf, "01234", 5));
}

TEST_F(VpiPutDataSim, MultipleWritesReadBackInDifferentChunkSizes) {
  const char kFirst[] = {'A', 'B', 'C'};
  const char kSecond[] = {'D', 'E', 'F'};
  DoubleWrite w;
  w.id = 3;
  w.first = kFirst;
  w.first_len = 3;
  w.second = kSecond;
  w.second_len = 3;
  DispatchWith(cbStartOfSave, WriteTwiceCb, &w);
  EXPECT_EQ(w.ret1, 3);
  EXPECT_EQ(w.ret2, 3);

  DoubleRead r;
  r.id = 3;
  r.req1 = 2;
  r.req2 = 4;
  DispatchWith(cbStartOfRestart, ReadTwiceCb, &r);

  EXPECT_EQ(r.ret1, 2);
  EXPECT_EQ(0, std::memcmp(r.buf1, "AB", 2));
  EXPECT_EQ(r.ret2, 4);
  EXPECT_EQ(0, std::memcmp(r.buf2, "CDEF", 4));
}

std::string g_location_in_save;
bool g_location_read_in_save = false;
bool g_location_read_outside = false;

int ReadLocationCb(s_cb_data*) {
  const char* path = vpi_get_str(vpiSaveRestartLocation, nullptr);
  g_location_read_in_save = path != nullptr;
  if (path != nullptr) g_location_in_save = path;
  return 0;
}

int ReadLocationOutsideCb(s_cb_data*) {
  g_location_read_outside =
      vpi_get_str(vpiSaveRestartLocation, nullptr) != nullptr;
  return 0;
}

TEST_F(VpiPutDataSim, TheSaveRestartLocationIsReadableFromASaveRoutine) {
  g_location_in_save.clear();
  g_location_read_in_save = false;
  vpi_ctx_.SetSaveRestartLocation("run.save");

  DispatchWith(cbStartOfSave, ReadLocationCb, nullptr);

  ASSERT_TRUE(g_location_read_in_save);
  EXPECT_EQ(g_location_in_save, "run.save");
}

TEST_F(VpiPutDataSim, TheSaveRestartLocationIsNotReadableElsewhere) {
  g_location_read_outside = false;
  vpi_ctx_.SetSaveRestartLocation("run.save");

  DispatchWith(cbEndOfSimulation, ReadLocationOutsideCb, nullptr);

  EXPECT_FALSE(g_location_read_outside);
}

TEST_F(VpiPutDataSim, TheSaveRestartLocationIsReadableAtTheEndOfASave) {
  g_location_in_save.clear();
  g_location_read_in_save = false;
  vpi_ctx_.SetSaveRestartLocation("end.save");

  DispatchWith(cbEndOfSave, ReadLocationCb, nullptr);

  ASSERT_TRUE(g_location_read_in_save);
  EXPECT_EQ(g_location_in_save, "end.save");
}

TEST_F(VpiPutDataSim, NoSaveRestartLocationIsReadAsNull) {
  g_location_read_in_save = true;

  DispatchWith(cbStartOfSave, ReadLocationCb, nullptr);

  EXPECT_FALSE(g_location_read_in_save);
}

}  // namespace
}  // namespace delta
