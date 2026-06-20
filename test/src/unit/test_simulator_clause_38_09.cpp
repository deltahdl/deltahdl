#include <gtest/gtest.h>

#include <cstring>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.9: vpi_get_data() is only legal from an application routine running for
// reason cbStartOfRestart or cbEndOfRestart. These probe routines stand in for
// such an application routine: the simulator invokes them from
// DispatchCallbacks (which sets the active callback reason), and they call
// vpi_get_data() and record what it returned.

// A single vpi_get_data() call.
struct SingleRead {
  int id = 0;
  int request = 0;
  int returned = -1;
  char buf[64] = {};
};

int ReadOnceCb(VpiCbData* cb) {
  auto* p = static_cast<SingleRead*>(cb->user_data);
  p->returned = vpi_get_data(p->id, p->buf, p->request);
  return 0;
}

// Reads with a null destination buffer, modeling an application that failed to
// provide the allocated storage the routine requires.
int ReadIntoNullCb(VpiCbData* cb) {
  auto* p = static_cast<SingleRead*>(cb->user_data);
  p->returned = vpi_get_data(p->id, nullptr, p->request);
  return 0;
}

// Two successive vpi_get_data() calls for the same id.
struct DoubleRead {
  int id = 0;
  int req1 = 0;
  int req2 = 0;
  int ret1 = -1;
  int ret2 = -1;
  char buf1[64] = {};
  char buf2[64] = {};
};

int ReadTwiceCb(VpiCbData* cb) {
  auto* p = static_cast<DoubleRead*>(cb->user_data);
  p->ret1 = vpi_get_data(p->id, p->buf1, p->req1);
  p->ret2 = vpi_get_data(p->id, p->buf2, p->req2);
  return 0;
}

class VpiGetDataSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Register `cb_rtn` for `reason`, carrying `probe`, then deliver it.
  void DispatchWith(int reason, int (*cb_rtn)(VpiCbData*), void* probe) {
    s_cb_data reg = {};
    reg.reason = reason;
    reg.cb_rtn = cb_rtn;
    reg.user_data = probe;
    ASSERT_NE(vpi_register_cb(&reg), nullptr);
    vpi_ctx_.DispatchCallbacks(reason);
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// §38.9: from a cbStartOfRestart routine the call shall place numOfBytes of the
// saved data into the caller's buffer and return the number of bytes retrieved.
TEST_F(VpiGetDataSim, ReadsSavedDataInsideStartOfRestart) {
  const char saved[] = {'D', 'e', 'l', 't', 'a'};
  vpi_ctx_.SeedSaveData(42, saved, 5);

  SingleRead probe;
  probe.id = 42;
  probe.request = 5;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &probe);

  EXPECT_EQ(probe.returned, 5);
  EXPECT_EQ(0, std::memcmp(probe.buf, saved, 5));
  // A clean read records no error (the C entry cleared the prior status).
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

// §38.9: the routine is equally legal from a cbEndOfRestart routine.
TEST_F(VpiGetDataSim, ReadsSavedDataInsideEndOfRestart) {
  const char saved[] = {'X', 'Y', 'Z'};
  vpi_ctx_.SeedSaveData(7, saved, 3);

  SingleRead probe;
  probe.id = 7;
  probe.request = 3;
  DispatchWith(cbEndOfRestart, ReadOnceCb, &probe);

  EXPECT_EQ(probe.returned, 3);
  EXPECT_EQ(0, std::memcmp(probe.buf, saved, 3));
}

// §38.9: the routine may only be called from a cbStartOfRestart/cbEndOfRestart
// routine. Called from any other context it fails, and a failure returns 0.
TEST_F(VpiGetDataSim, RejectedOutsideRestartCallback) {
  const char saved[] = {'a', 'b', 'c', 'd'};
  vpi_ctx_.SeedSaveData(1, saved, 4);

  char buf[8] = {};
  int returned = vpi_get_data(1, buf, 4);  // no callback active

  EXPECT_EQ(returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// §38.9: the first call for an id reads from the start of the saved data, and
// each subsequent call resumes where the previous call left off.
TEST_F(VpiGetDataSim, SequentialReadsResumeWhereLeftOff) {
  const char saved[] = {'0', '1', '2', '3', '4', '5'};
  vpi_ctx_.SeedSaveData(9, saved, 6);

  DoubleRead probe;
  probe.id = 9;
  probe.req1 = 2;
  probe.req2 = 3;
  DispatchWith(cbStartOfRestart, ReadTwiceCb, &probe);

  EXPECT_EQ(probe.ret1, 2);
  EXPECT_EQ(0, std::memcmp(probe.buf1, "01", 2));
  EXPECT_EQ(probe.ret2, 3);
  // Resumes at offset 2, not back at the start.
  EXPECT_EQ(0, std::memcmp(probe.buf2, "234", 3));
}

// §38.9: requesting more data than were saved is a warning. The bytes that are
// left are delivered, the remainder of the buffer is zero-filled, and the
// return value is the number of bytes actually retrieved.
TEST_F(VpiGetDataSim, RetrievingMoreThanStoredWarnsAndZeroFills) {
  const char saved[] = {'h', 'i'};
  vpi_ctx_.SeedSaveData(3, saved, 2);

  SingleRead probe;
  probe.id = 3;
  probe.request = 5;
  std::memset(probe.buf, '?', sizeof(probe.buf));
  DispatchWith(cbStartOfRestart, ReadOnceCb, &probe);

  EXPECT_EQ(probe.returned, 2);  // actual bytes retrieved, not 5
  EXPECT_EQ(probe.buf[0], 'h');
  EXPECT_EQ(probe.buf[1], 'i');
  EXPECT_EQ(probe.buf[2], '\0');  // remaining bytes zero-filled
  EXPECT_EQ(probe.buf[3], '\0');
  EXPECT_EQ(probe.buf[4], '\0');
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiWarning);
}

// §38.9: it shall be acceptable to retrieve fewer bytes than were saved; the
// short read succeeds and reports no error.
TEST_F(VpiGetDataSim, RetrievingLessThanStoredIsAcceptable) {
  const char saved[] = {'p', 'q', 'r', 's'};
  vpi_ctx_.SeedSaveData(5, saved, 4);

  SingleRead probe;
  probe.id = 5;
  probe.request = 2;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &probe);

  EXPECT_EQ(probe.returned, 2);
  EXPECT_EQ(0, std::memcmp(probe.buf, "pq", 2));
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

// §38.9: an id that was never saved cannot be retrieved; the failure returns 0.
TEST_F(VpiGetDataSim, UnknownIdReturnsZero) {
  SingleRead probe;
  probe.id = 999;  // never seeded
  probe.request = 4;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &probe);

  EXPECT_EQ(probe.returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// §38.9: the destination memory must be supplied by the application. A null
// destination has nowhere to place the data, so the call fails and returns 0,
// distinct from the warning path taken when the buffer is valid but oversized.
TEST_F(VpiGetDataSim, NullDestinationInsideRestartReturnsZero) {
  const char saved[] = {'m', 'n', 'o'};
  vpi_ctx_.SeedSaveData(11, saved, 3);

  SingleRead probe;
  probe.id = 11;
  probe.request = 3;
  DispatchWith(cbStartOfRestart, ReadIntoNullCb, &probe);

  EXPECT_EQ(probe.returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// §38.9: once an id's saved data has been fully consumed, a further read finds
// nothing left. This is the boundary of the over-read case: zero bytes are
// retrieved, the buffer is entirely zero-filled, the return value is 0, and it
// is reported as a warning rather than an error.
TEST_F(VpiGetDataSim, ReadingPastEndOfSavedDataWarnsAndZeroFills) {
  const char saved[] = {'A', 'B', 'C'};
  vpi_ctx_.SeedSaveData(13, saved, 3);

  DoubleRead probe;
  probe.id = 13;
  probe.req1 = 3;  // first read consumes everything
  probe.req2 = 2;  // second read starts at the exhausted cursor
  std::memset(probe.buf2, '?', sizeof(probe.buf2));
  DispatchWith(cbStartOfRestart, ReadTwiceCb, &probe);

  EXPECT_EQ(probe.ret1, 3);
  EXPECT_EQ(0, std::memcmp(probe.buf1, "ABC", 3));
  EXPECT_EQ(probe.ret2, 0);        // nothing left to retrieve
  EXPECT_EQ(probe.buf2[0], '\0');  // buffer zero-filled, not left as '?'
  EXPECT_EQ(probe.buf2[1], '\0');
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiWarning);
}

}  // namespace
}  // namespace delta
