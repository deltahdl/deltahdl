#include <gtest/gtest.h>

#include <cstring>

#include "helpers_vpi_save_restore_probe.h"

namespace delta {
namespace {

// §38.9: vpi_get_data() is only legal from an application routine running for
// reason cbStartOfRestart or cbEndOfRestart. The probe routines and fixture
// that drive these reads live in helpers_vpi_save_restore_probe.h.

// A single vpi_put_data() call, which §38.31 makes legal only from a
// cbStartOfSave or cbEndOfSave application routine -- the same shape the read
// probes in helpers_vpi_save_restore_probe.h have for the same reason on the
// other side.
struct SingleWrite {
  int id = 0;
  char* data = nullptr;
  int len = 0;
};

inline int WriteOnceCb(VpiCbData* cb) {
  auto* p = static_cast<SingleWrite*>(cb->user_data);
  vpi_put_data(p->id, p->data, p->len);
  return 0;
}

// Reads with a null destination buffer, modeling an application that failed to
// provide the allocated storage the routine requires.
int ReadIntoNullCb(VpiCbData* cb) {
  auto* p = static_cast<SingleRead*>(cb->user_data);
  p->returned = vpi_get_data(p->id, nullptr, p->request);
  return 0;
}

using VpiGetDataSim = VpiSaveRestoreSim;

// §38.9: from a cbStartOfRestart routine the call shall place numOfBytes of the
// saved data into the caller's buffer and return the number of bytes retrieved.
TEST_F(VpiGetDataSim, ReadsSavedDataInsideStartOfRestart) {
  const char kSaved[] = {'D', 'e', 'l', 't', 'a'};
  vpi_ctx_.SeedSaveData(42, kSaved, 5);

  SingleRead probe;
  probe.id = 42;
  probe.request = 5;
  DispatchWith(cbStartOfRestart, ReadOnceCb, &probe);

  EXPECT_EQ(probe.returned, 5);
  EXPECT_EQ(0, std::memcmp(probe.buf, kSaved, 5));
  // A clean read records no error (the C entry cleared the prior status).
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

// §38.9: the routine is equally legal from a cbEndOfRestart routine.
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

// §38.9: the routine may only be called from a cbStartOfRestart/cbEndOfRestart
// routine. Called from any other context it fails, and a failure returns 0.
TEST_F(VpiGetDataSim, RejectedOutsideRestartCallback) {
  const char kSaved[] = {'a', 'b', 'c', 'd'};
  vpi_ctx_.SeedSaveData(1, kSaved, 4);

  char buf[8] = {};
  int returned = vpi_get_data(1, buf, 4);  // no callback active

  EXPECT_EQ(returned, 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// §38.9: the first call for an id reads from the start of the saved data, and
// each subsequent call resumes where the previous call left off.
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
  // Resumes at offset 2, not back at the start.
  EXPECT_EQ(0, std::memcmp(probe.buf2, "234", 3));
}

// §38.9: requesting more data than were saved is a warning. The bytes that are
// left are delivered, the remainder of the buffer is zero-filled, and the
// return value is the number of bytes actually retrieved.
TEST_F(VpiGetDataSim, RetrievingMoreThanStoredWarnsAndZeroFills) {
  const char kSaved[] = {'h', 'i'};
  vpi_ctx_.SeedSaveData(3, kSaved, 2);

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
  const char kSaved[] = {'m', 'n', 'o'};
  vpi_ctx_.SeedSaveData(11, kSaved, 3);

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
  const char kSaved[] = {'A', 'B', 'C'};
  vpi_ctx_.SeedSaveData(13, kSaved, 3);

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

// §38.9 names where the first of vpi_get_data()'s three arguments comes from:
// the id is "a save/restart ID returned from vpi_get(vpiSaveRestartID, NULL)".
// That query answered with the 0 an unknown property gets, which is the one
// value vpi_get_data() and vpi_put_data() refuse, so an application following
// the clause could not obtain an id to save under at all -- every case above
// picks a number of its own and seeds the store behind the routine's back.
TEST_F(VpiGetDataSim, TheIdIsTheOneTheToolHandsBack) {
  int id = vpi_get(vpiSaveRestartID, nullptr);
  ASSERT_NE(id, 0);

  // §38.9: "the first call for a given id will retrieve the data starting at
  // what was placed into the save/restart location with the first call to
  // vpi_put_data() for a given id." So the data goes in under that id and comes
  // back out under it, which is the whole of the clause's own flow.
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

}  // namespace
}  // namespace delta
