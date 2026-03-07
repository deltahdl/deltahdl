#include "fixture_simulator.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// §8.30.1: WeakReference default state is null.
TEST(ClassSim, WeakReferenceDefaultNull) {
  WeakReference wr;
  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

// §8.30.1: WeakReference stores a referent handle.
TEST(ClassSim, WeakReferenceStoresReferent) {
  WeakReference wr;
  wr.referent_handle = 42;
  EXPECT_EQ(wr.Get(), 42u);
}

}  // namespace
