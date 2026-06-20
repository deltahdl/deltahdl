#include <gtest/gtest.h>

#include <cstring>

#include "helpers_vpi_save_restore_probe.h"

namespace delta {
namespace {

// §38.31: vpi_put_data() is only legal from an application routine running for
// reason cbStartOfSave or cbEndOfSave. These probe routines stand in for such
// an application routine: the simulator invokes them from DispatchCallbacks
// (which sets the active callback reason), and they call vpi_put_data() and
// record what it returned. The companion read probes and the fixture used to
// observe what was written (vpi_get_data(), §38.9) live in
// helpers_vpi_save_restore_probe.h.

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

using VpiPutDataSim = VpiSaveRestoreSim;

// §38.31 C1+C2: from a cbStartOfSave routine the call shall place numOfBytes of
// data into the implementation's save/restart location, and the return value
// shall be the number of bytes written. The bytes are observed by reading them
// back with vpi_get_data() under a restart reason.
TEST_F(VpiPutDataSim, WritesDataInsideStartOfSave) {
  const char kPayload[] = {'D', 'e', 'l', 't', 'a'};
  SingleWrite w;
  w.id = 42;
  w.data = kPayload;
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
  EXPECT_EQ(0, std::memcmp(r.buf, kPayload, 5));
}

// §38.31 C6: the routine is equally legal from a cbEndOfSave routine.
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

// §38.31 C6: the routine can only be called from a cbStartOfSave/cbEndOfSave
// routine. Called from any other context it fails (an error is detected) and
// per C3 a failure returns zero.
TEST_F(VpiPutDataSim, RejectedOutsideSaveCallback) {
  const char kPayload[] = {'a', 'b', 'c', 'd'};
  int returned =
      vpi_put_data(1, const_cast<char*>(kPayload), 4);  // no callback

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
  const char kPayload[] = {'w', 'x', 'y', 'z'};
  SingleWrite w;
  w.id = 21;
  w.data = kPayload;
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
  const char kPayload[] = {'q'};
  SingleWrite w;
  w.id = 5;
  w.data = kPayload;
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
  const char kFirst[] = {'A', 'B', 'C'};
  const char kSecond[] = {'D', 'E', 'F'};
  SingleWrite w1;
  w1.id = 3;
  w1.data = kFirst;
  w1.len = 3;
  DispatchWith(cbStartOfSave, WriteOnceCb, &w1);
  SingleWrite w2;
  w2.id = 3;
  w2.data = kSecond;
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
