#include "fixture_simulator.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, WeakReferenceDefaultNull) {
  WeakReference wr;
  EXPECT_EQ(wr.Get(), kNullClassHandle);
}

TEST(ClassSim, WeakReferenceStoresReferent) {
  WeakReference wr;
  wr.referent_handle = 42;
  EXPECT_EQ(wr.Get(), 42u);
}

}
