#include <gtest/gtest.h>

#include <cstring>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.31: vpi_put_data() is only legal from an application routine running for
// reason cbStartOfSave or cbEndOfSave. These probe routines stand in for such
// an application routine: the simulator invokes them from DispatchCallbacks
// (which sets the active callback reason), and they call vpi_put_data() and
// record what it returned.

// A single vpi_put_data() call.
struct SingleWrite {
  int id = 0;
  const char* data = nullptr;
  int len = 0;
  int returned = -1;
};

int WriteOnceCb(VpiCbData* cb) {
  auto* p = static_cast<SingleWrite*>(cb->user_data);
  p->returned = vpi_put_data(p->id, const_cast<char*>(p->data), p->len);
  return 0;
}

// A vpi_put_data() call made with a null source buffer.
int WriteFromNullCb(VpiCbData* cb) {
  auto* p = static_cast<SingleWrite*>(cb->user_data);
  p->returned = vpi_put_data(p->id, nullptr, p->len);
  return 0;
}

// Two successive vpi_put_data() calls for the same id, then a third for a
// different id, exercising repeated and interleaved writes.
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

int WriteInterleavedCb(VpiCbData* cb) {
  auto* p = static_cast<MultiWrite*>(cb->user_data);
  p->ret_a1 = vpi_put_data(p->id_a, const_cast<char*>(p->a1), p->a1_len);
  p->ret_b = vpi_put_data(p->id_b, const_cast<char*>(p->b), p->b_len);
  p->ret_a2 = vpi_put_data(p->id_a, const_cast<char*>(p->a2), p->a2_len);
  return 0;
}

// A single read used to observe what was written; runs under a restart reason
// because vpi_get_data() (§38.9) is only legal there.
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

// Two reads of different chunk sizes for the same id, used to show stored data
// can be pulled out in chunks of any size.
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

class VpiPutDataSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Register `cb_rtn` for `reason`, carrying `probe`, then deliver it. The
  // dispatch sets the active callback reason for the duration of the routine.
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

// §38.31 C1+C2: from a cbStartOfSave routine the call shall place numOfBytes of
// data into the implementation's save/restart location, and the return value
// shall be the number of bytes written. The bytes are observed by reading them
// back with vpi_get_data() under a restart reason.
TEST_F(VpiPutDataSim, WritesDataInsideStartOfSave) {
  const char payload[] = {'D', 'e', 'l', 't', 'a'};
  SingleWrite w;
  w.id = 42;
  w.data = payload;
  w.len = 5;
  DispatchWith(cbStartOfSave, WriteOnceCb, &w);

  EXPECT_EQ(w.returned, 5);  // number of bytes written
  // A clean write records no error (the C entry cleared the prior status).
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);

  SingleRead r;
  r.id = 42;
  r.request = 5;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &r);
  EXPECT_EQ(r.returned, 5);
  EXPECT_EQ(0, std::memcmp(r.buf, payload, 5));
}

// §38.31 C6: the routine is equally legal from a cbEndOfSave routine.
TEST_F(VpiPutDataSim, WritesDataInsideEndOfSave) {
  const char payload[] = {'X', 'Y', 'Z'};
  SingleWrite w;
  w.id = 7;
  w.data = payload;
  w.len = 3;
  DispatchWith(cbEndOfSave, WriteOnceCb, &w);

  EXPECT_EQ(w.returned, 3);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

// §38.31 C6: the routine can only be called from a cbStartOfSave/cbEndOfSave
// routine. Called from any other context it fails (an error is detected) and
// per C3 a failure returns zero.
TEST_F(VpiPutDataSim, RejectedOutsideSaveCallback) {
  const char payload[] = {'a', 'b', 'c', 'd'};
  int returned = vpi_put_data(1, const_cast<char*>(payload), 4);  // no callback

  EXPECT_EQ(returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);

  // The rejected write stored nothing: a later restart read finds no data.
  SingleRead r;
  r.id = 1;
  r.request = 4;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &r);
  EXPECT_EQ(r.returned, 0);
}

// §38.31 C6 edge: the allowed reasons are specifically the save reasons. A
// callback IS active here, but it is a restart reason (the reason that makes
// the companion reader vpi_get_data() legal, §38.9). The writer must still
// reject it, distinguishing "a save callback is running" from merely "some
// callback is running". Per C3 the rejection returns zero.
TEST_F(VpiPutDataSim, RejectedInsideNonSaveCallback) {
  const char payload[] = {'w', 'x', 'y', 'z'};
  SingleWrite w;
  w.id = 21;
  w.data = payload;
  w.len = 4;
  DispatchWith(cbStartOfRestart, WriteOnceCb, &w);

  EXPECT_EQ(w.returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);

  // Nothing was stored under the id: a later restart read finds no data.
  SingleRead r;
  r.id = 21;
  r.request = 4;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &r);
  EXPECT_EQ(r.returned, 0);
}

// §38.31 C1+C3: numOfBytes shall be greater than zero. A non-positive count is
// a detected error and returns zero.
TEST_F(VpiPutDataSim, NonPositiveCountReturnsZero) {
  const char payload[] = {'q'};
  SingleWrite w;
  w.id = 5;
  w.data = payload;
  w.len = 0;  // not greater than zero
  DispatchWith(cbStartOfSave, WriteOnceCb, &w);

  EXPECT_EQ(w.returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// §38.31 C1+C3: the source storage must be supplied by the application. A null
// dataLoc is a detected error and returns zero.
TEST_F(VpiPutDataSim, NullSourceReturnsZero) {
  SingleWrite w;
  w.id = 8;
  w.len = 4;
  DispatchWith(cbStartOfSave, WriteFromNullCb, &w);

  EXPECT_EQ(w.returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// §38.31 C4: there shall be no restriction on how many times the routine is
// called for a given id, nor on the order in which ids are written. Two writes
// to one id are interleaved with a write to another; each succeeds and reports
// its own byte count.
TEST_F(VpiPutDataSim, RepeatedAndInterleavedWritesAreUnrestricted) {
  const char a1[] = {'0', '1'};
  const char b[] = {'!', '?'};
  const char a2[] = {'2', '3', '4'};
  MultiWrite w;
  w.id_a = 9;
  w.id_b = 10;
  w.a1 = a1;
  w.a1_len = 2;
  w.b = b;
  w.b_len = 2;
  w.a2 = a2;
  w.a2_len = 3;
  DispatchWith(cbStartOfSave, WriteInterleavedCb, &w);

  EXPECT_EQ(w.ret_a1, 2);
  EXPECT_EQ(w.ret_b, 2);
  EXPECT_EQ(w.ret_a2, 3);

  // id_a accumulated both of its writes, in order, undisturbed by the id_b
  // write that landed between them.
  SingleRead ra;
  ra.id = 9;
  ra.request = 5;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &ra);
  EXPECT_EQ(ra.returned, 5);
  EXPECT_EQ(0, std::memcmp(ra.buf, "01234", 5));
}

// §38.31 C5: data from multiple calls with the same id shall be stored so that
// vpi_get_data() can pull it back out using different sizes of chunks. Here two
// writes establish six bytes, retrieved as a 2-byte chunk followed by a 4-byte
// chunk that crosses the boundary between the two writes.
TEST_F(VpiPutDataSim, MultipleWritesReadBackInDifferentChunkSizes) {
  const char first[] = {'A', 'B', 'C'};
  const char second[] = {'D', 'E', 'F'};
  SingleWrite w1;
  w1.id = 3;
  w1.data = first;
  w1.len = 3;
  DispatchWith(cbStartOfSave, WriteOnceCb, &w1);
  SingleWrite w2;
  w2.id = 3;
  w2.data = second;
  w2.len = 3;
  DispatchWith(cbStartOfSave, WriteOnceCb, &w2);

  DoubleRead r;
  r.id = 3;
  r.req1 = 2;  // chunk one
  r.req2 = 4;  // chunk two, spans the two original writes
  DispatchWith(cbStartOfRestart, ReadTwiceCb, &r);

  EXPECT_EQ(r.ret1, 2);
  EXPECT_EQ(0, std::memcmp(r.buf1, "AB", 2));
  EXPECT_EQ(r.ret2, 4);
  EXPECT_EQ(0, std::memcmp(r.buf2, "CDEF", 4));
}

}  // namespace
}  // namespace delta
