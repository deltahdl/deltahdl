#include <gtest/gtest.h>

#include <cstring>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiMcdNameSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;

  // mcd channel 32 is the MSB, which marks an fd returned from $fopen.
  static constexpr PLI_UINT32 kMsbChannel = 0x80000000u;
};

// §38.26: vpi_mcd_name() shall return the name of the file represented by a
// single-channel descriptor. A file opened with vpi_mcd_open() is named back by
// the descriptor that open returned.
TEST_F(VpiMcdNameSim, ReturnsNameOfFileNamedByDescriptor) {
  char name[] = "trace.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  PLI_BYTE8* reported = vpi_mcd_name(mcd);
  ASSERT_NE(reported, nullptr);
  EXPECT_STREQ(reported, "trace.log");
}

// §38.26: the routine can get the name of a file opened by $fopen, whose
// descriptor lives in the shared namespace. Such a descriptor could be an fd
// with its MSB set; the name is still reported.
TEST_F(VpiMcdNameSim, ReportsNameOfFopenFileIncludingFdWithMsbSet) {
  PLI_UINT32 fd = kMsbChannel | 0x5u;  // an fd from $fopen has its MSB set
  vpi_ctx_.RegisterFopenMcdFile("from_fopen.log", fd);

  PLI_BYTE8* reported = vpi_mcd_name(fd);
  ASSERT_NE(reported, nullptr);
  EXPECT_STREQ(reported, "from_fopen.log");
}

// §38.26: on error the routine shall return NULL. A descriptor of 0 and a
// descriptor that names no open file both take the error return.
TEST_F(VpiMcdNameSim, ReturnsNullOnError) {
  EXPECT_EQ(vpi_mcd_name(0u), nullptr);

  // A channel that was never opened names nothing.
  EXPECT_EQ(vpi_mcd_name(0x00000008u), nullptr);
}

// §38.26: the routine shall overwrite the returned value on subsequent calls -
// it hands back one reused buffer, so a pointer from an earlier call no longer
// reads as the file it first named once a later call has run. A caller that
// needs to retain the string must copy it.
TEST_F(VpiMcdNameSim, OverwritesReturnedValueOnSubsequentCalls) {
  // Equal-length names so the reused buffer keeps the same allocation and the
  // earlier pointer stays valid to observe the overwrite.
  char a[] = "alpha.log";
  char b[] = "bravo.log";
  PLI_UINT32 mcd_a = vpi_mcd_open(a);
  PLI_UINT32 mcd_b = vpi_mcd_open(b);
  ASSERT_NE(mcd_a, 0u);
  ASSERT_NE(mcd_b, 0u);

  PLI_BYTE8* first = vpi_mcd_name(mcd_a);
  ASSERT_NE(first, nullptr);
  // The application copies the string it wants to keep, as the clause advises.
  std::string retained(first);
  EXPECT_EQ(retained, "alpha.log");

  PLI_BYTE8* second = vpi_mcd_name(mcd_b);
  ASSERT_NE(second, nullptr);
  // Same reused buffer, and reading the first pointer now shows the later name:
  // the returned value was overwritten in place.
  EXPECT_EQ(second, first);
  EXPECT_STREQ(first, "bravo.log");
  // The earlier copy is unaffected, demonstrating why a caller must copy.
  EXPECT_EQ(retained, "alpha.log");
}

}  // namespace
}  // namespace delta
