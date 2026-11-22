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

struct CarriedId {
  int restart_reason = 0;
  int id = 0;
  int returned = -1;
  char buf[8] = {};
};

CarriedId* carried = nullptr;

int ReadUnderTheCarriedIdCb(s_cb_data* cb) {
  const int kId = *reinterpret_cast<int*>(cb->user_data);
  carried->returned = vpi_get_data(kId, carried->buf, 3);
  return 0;
}

int SaveAndArmTheRestartCb(s_cb_data*) {
  const int kId = vpi_get(vpiSaveRestartID, nullptr);
  char data[] = {'s', 'a', 'v'};
  vpi_put_data(kId, data, 3);
  carried->id = kId;
  s_cb_data reg = {};
  reg.reason = carried->restart_reason;
  reg.cb_rtn = ReadUnderTheCarriedIdCb;
  reg.user_data = reinterpret_cast<PLI_BYTE8*>(&carried->id);
  vpi_register_cb(&reg);
  return 0;
}

class SaveRoutineCarriesItsId : public VpiGetDataSim {
 protected:
  void ExpectTheRestartReadsTheSave(int save_reason, int restart_reason) {
    CarriedId probe;
    probe.restart_reason = restart_reason;
    carried = &probe;
    DispatchWith(save_reason, SaveAndArmTheRestartCb, nullptr);
    vpi_ctx_.DispatchRestart();
    EXPECT_EQ(probe.returned, 3);
    EXPECT_EQ(0, std::memcmp(probe.buf, "sav", 3));
    carried = nullptr;
  }
};

TEST_F(SaveRoutineCarriesItsId, FromStartOfSaveToStartOfRestart) {
  ExpectTheRestartReadsTheSave(cbStartOfSave, cbStartOfRestart);
}

TEST_F(SaveRoutineCarriesItsId, FromEndOfSaveToEndOfRestart) {
  ExpectTheRestartReadsTheSave(cbEndOfSave, cbEndOfRestart);
}

TEST_F(VpiGetDataSim, RefusedFromARoutineOfAnyOtherReason) {
  const char kSaved[] = {'o', 'k'};
  for (const int kReason :
       {cbStartOfSave, cbEndOfSave, cbStartOfSimulation, cbEndOfSimulation}) {
    vpi_ctx_.SeedSaveData(11, kSaved, 2);
    SingleRead probe;
    probe.id = 11;
    probe.request = 2;
    DispatchWith(kReason, ReadOnceCb, &probe);
    EXPECT_EQ(probe.returned, 0) << kReason;
    EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError) << kReason;
  }
}

TEST_F(VpiGetDataSim, AnOverReadFromPartwayDeliversWhatIsLeft) {
  const char kSaved[] = {'a', 'b', 'c', 'd', 'e'};
  vpi_ctx_.SeedSaveData(4, kSaved, 5);

  DoubleRead probe;
  probe.id = 4;
  probe.req1 = 2;
  probe.req2 = 6;
  std::memset(probe.buf2, '?', sizeof(probe.buf2));
  DispatchWith(cbStartOfRestart, ReadTwiceCb, &probe);

  EXPECT_EQ(probe.ret1, 2);
  EXPECT_EQ(probe.ret2, 3);
  EXPECT_EQ(0, std::memcmp(probe.buf2, "cde\0\0\0", 6));
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiWarning);
}

TEST_F(VpiGetDataSim, AnOverReadOfWhatASaveRoutinePutWarnsAndZeroFills) {
  const int kId = vpi_get(vpiSaveRestartID, nullptr);
  char saved[] = {'p', 'u'};
  SingleWrite write;
  write.id = kId;
  write.data = saved;
  write.len = 2;
  DispatchWith(cbEndOfSave, WriteOnceCb, &write);

  SingleRead probe;
  probe.id = kId;
  probe.request = 5;
  std::memset(probe.buf, '?', sizeof(probe.buf));
  DispatchWith(cbStartOfRestart, ReadOnceCb, &probe);

  EXPECT_EQ(probe.returned, 2);
  EXPECT_EQ(0, std::memcmp(probe.buf, "pu\0\0\0", 5));
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiWarning);
}

struct InterleavedReads {
  int returned[4] = {-1, -1, -1, -1};
  char buf[4][4] = {};
};

int ReadTwoIdsInTurnCb(s_cb_data* cb) {
  auto* p = reinterpret_cast<InterleavedReads*>(cb->user_data);
  const int kIds[] = {21, 22, 21, 22};
  for (int i = 0; i < 4; ++i) {
    p->returned[i] = vpi_get_data(kIds[i], p->buf[i], 2);
  }
  return 0;
}

TEST_F(VpiGetDataSim, InterleavedIdsEachResumeFromTheirOwnPosition) {
  vpi_ctx_.SeedSaveData(21, "ABCD", 4);
  vpi_ctx_.SeedSaveData(22, "wxyz", 4);

  InterleavedReads probe;
  DispatchWith(cbStartOfRestart, ReadTwoIdsInTurnCb, &probe);

  for (const int kReturned : probe.returned) EXPECT_EQ(kReturned, 2);
  EXPECT_EQ(0, std::memcmp(probe.buf[0], "AB", 2));
  EXPECT_EQ(0, std::memcmp(probe.buf[1], "wx", 2));
  EXPECT_EQ(0, std::memcmp(probe.buf[2], "CD", 2));
  EXPECT_EQ(0, std::memcmp(probe.buf[3], "yz", 2));
}

}  // namespace
}  // namespace delta
