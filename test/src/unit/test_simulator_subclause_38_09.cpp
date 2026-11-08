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
  char* data = nullptr;
  int len = 0;
};

inline int WriteOnceCb(s_cb_data* cb) {
  auto* p = reinterpret_cast<SingleWrite*>(cb->user_data);
  vpi_put_data(p->id, p->data, p->len);
  return 0;
}

int ReadIntoNullCb(s_cb_data* cb) {
  auto* p = reinterpret_cast<SingleRead*>(cb->user_data);
  p->returned = vpi_get_data(p->id, nullptr, p->request);
  return 0;
}

using VpiGetDataSim = VpiSaveRestoreSim;

TEST_F(VpiGetDataSim, ReadsSavedDataInsideStartOfRestart) {
  const char kSaved[] = {'D', 'e', 'l', 't', 'a'};
  vpi_ctx_.SeedSaveData(42, kSaved, 5);

  SingleRead probe;
  probe.id = 42;
  probe.request = 5;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &probe);

  EXPECT_EQ(probe.returned, 5);
  EXPECT_EQ(0, std::memcmp(probe.buf, kSaved, 5));
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

TEST_F(VpiGetDataSim, ReadsSavedDataInsideEndOfRestart) {
  const char kSaved[] = {'X', 'Y', 'Z'};
  vpi_ctx_.SeedSaveData(7, kSaved, 3);

  SingleRead probe;
  probe.id = 7;
  probe.request = 3;
  DispatchWith(cbEndOfRestart, ReadOnceCb, &probe);

  EXPECT_EQ(probe.returned, 3);
  EXPECT_EQ(0, std::memcmp(probe.buf, kSaved, 3));
}

TEST_F(VpiGetDataSim, RejectedOutsideRestartCallback) {
  const char kSaved[] = {'a', 'b', 'c', 'd'};
  vpi_ctx_.SeedSaveData(1, kSaved, 4);

  char buf[8] = {};
  int returned = vpi_get_data(1, buf, 4);

  EXPECT_EQ(returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

TEST_F(VpiGetDataSim, SequentialReadsResumeWhereLeftOff) {
  const char kSaved[] = {'0', '1', '2', '3', '4', '5'};
  vpi_ctx_.SeedSaveData(9, kSaved, 6);

  DoubleRead probe;
  probe.id = 9;
  probe.req1 = 2;
  probe.req2 = 3;
  DispatchWith(cbStartOfRestart, ReadTwiceCb, &probe);

  EXPECT_EQ(probe.ret1, 2);
  EXPECT_EQ(0, std::memcmp(probe.buf1, "01", 2));
  EXPECT_EQ(probe.ret2, 3);
  EXPECT_EQ(0, std::memcmp(probe.buf2, "234", 3));
}

TEST_F(VpiGetDataSim, RetrievingMoreThanStoredWarnsAndZeroFills) {
  const char kSaved[] = {'h', 'i'};
  vpi_ctx_.SeedSaveData(3, kSaved, 2);

  SingleRead probe;
  probe.id = 3;
  probe.request = 5;
  std::memset(probe.buf, '?', sizeof(probe.buf));
  DispatchWith(cbStartOfRestart, ReadOnceCb, &probe);

  EXPECT_EQ(probe.returned, 2);
  EXPECT_EQ(probe.buf[0], 'h');
  EXPECT_EQ(probe.buf[1], 'i');
  EXPECT_EQ(probe.buf[2], '\0');
  EXPECT_EQ(probe.buf[3], '\0');
  EXPECT_EQ(probe.buf[4], '\0');
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiWarning);
}

TEST_F(VpiGetDataSim, RetrievingLessThanStoredIsAcceptable) {
  const char kSaved[] = {'p', 'q', 'r', 's'};
  vpi_ctx_.SeedSaveData(5, kSaved, 4);

  SingleRead probe;
  probe.id = 5;
  probe.request = 2;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &probe);

  EXPECT_EQ(probe.returned, 2);
  EXPECT_EQ(0, std::memcmp(probe.buf, "pq", 2));
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

TEST_F(VpiGetDataSim, UnknownIdReturnsZero) {
  SingleRead probe;
  probe.id = 999;
  probe.request = 4;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &probe);

  EXPECT_EQ(probe.returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

TEST_F(VpiGetDataSim, NullDestinationInsideRestartReturnsZero) {
  const char kSaved[] = {'m', 'n', 'o'};
  vpi_ctx_.SeedSaveData(11, kSaved, 3);

  SingleRead probe;
  probe.id = 11;
  probe.request = 3;
  DispatchWith(cbStartOfRestart, ReadIntoNullCb, &probe);

  EXPECT_EQ(probe.returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

TEST_F(VpiGetDataSim, ReadingPastEndOfSavedDataWarnsAndZeroFills) {
  const char kSaved[] = {'A', 'B', 'C'};
  vpi_ctx_.SeedSaveData(13, kSaved, 3);

  DoubleRead probe;
  probe.id = 13;
  probe.req1 = 3;
  probe.req2 = 2;
  std::memset(probe.buf2, '?', sizeof(probe.buf2));
  DispatchWith(cbStartOfRestart, ReadTwiceCb, &probe);

  EXPECT_EQ(probe.ret1, 3);
  EXPECT_EQ(0, std::memcmp(probe.buf1, "ABC", 3));
  EXPECT_EQ(probe.ret2, 0);
  EXPECT_EQ(probe.buf2[0], '\0');
  EXPECT_EQ(probe.buf2[1], '\0');
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiWarning);
}

TEST_F(VpiGetDataSim, TheIdIsTheOneTheToolHandsBack) {
  int id = vpi_get(vpiSaveRestartID, nullptr);
  ASSERT_NE(id, 0);

  char saved[] = {'i', 'd'};
  SingleWrite write;
  write.id = id;
  write.data = saved;
  write.len = 2;
  DispatchWith(cbStartOfSave, WriteOnceCb, &write);

  SingleRead probe;
  probe.id = id;
  probe.request = 2;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &probe);

  EXPECT_EQ(probe.returned, 2);
  EXPECT_EQ(0, std::memcmp(probe.buf, saved, 2));
}

TEST_F(VpiGetDataSim, NoBytesAreSavedOrRead) {
  const char kSaved[] = {'x', 'y'};
  vpi_ctx_.SeedSaveData(5, nullptr, 2);
  vpi_ctx_.SeedSaveData(5, kSaved, 0);
  SingleRead unsaved;
  unsaved.id = 5;
  unsaved.request = 1;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &unsaved);
  EXPECT_EQ(unsaved.returned, 0);

  vpi_ctx_.SeedSaveData(6, kSaved, 2);
  SingleRead nothing;
  nothing.id = 6;
  nothing.request = 0;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &nothing);
  EXPECT_EQ(nothing.returned, 0);
}

int ReadRestartLocationCb(s_cb_data* cb) {
  const char* path = vpi_get_str(vpiSaveRestartLocation, nullptr);
  *reinterpret_cast<std::string*>(cb->user_data) =
      path != nullptr ? path : "(none)";
  return 0;
}

TEST_F(VpiGetDataSim, TheSaveRestartLocationIsReadableFromARestartRoutine) {
  vpi_ctx_.SetSaveRestartLocation("run.save");
  for (int reason : {cbStartOfRestart, cbEndOfRestart}) {
    std::string location;
    DispatchWith(reason, ReadRestartLocationCb, &location);
    EXPECT_EQ(location, "run.save") << reason;
  }
}

}  // namespace
}  // namespace delta
